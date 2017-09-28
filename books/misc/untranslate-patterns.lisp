; Simple, Pattern-Based Untranslation for ACL2
; Copyright (C) 2005-2008 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>
; Slightly modified by Shilpi Goel <shigoel@cs.utexas.edu> to add
; define's untranslator

(in-package "ACL2")
(include-book "symbol-btree")
(include-book "std/util/define" :dir :system)
(include-book "xdoc/top" :dir :system)


;; Simple, Pattern-Based Untranslation
;;
;; This file provides an untranslate preprocessor (see :doc user-defined-
;; functions-table in ACL2 2.9.2 or above) which allows you to add pattern-
;; driven rules for performing custom translation.
;;
;; Patterns and replacements are stored as rules in a database, which can
;; be easily extended using the add-untranslate-pattern macro.  The database
;; uses an alist and a symbol-btree to store the patterns, so you may
;; occasionally wish to rebalance the tree and clean up the alist, using
;; the macro (optimize-untranslate-patterns).
;;
;; See :doc untranslate-patterns-table or :doc add-untranslate-pattern after
;; loading this file for usage examples.

(defxdoc untranslate-patterns
  :parents (macros user-defined-functions-table)
  :short "A database used to extend @('untranslate'), ACL2's function for
displaying terms during proofs, with pattern-based rules."

  :long "<p>The @('untranslate-patterns-table') is an ACL2 @(see table) that
stores patterns and replacements for use at untranslate time.  That is, during
proof output, this table is consulted before printing terms, allowing for
custom printing of particular terms.</p>

<p>Although this table has nothing to do with soundness, the rules it lists are
intended to obey the untranslate contract&mdash;that is, the replacements
listed for each pattern should macro-expand to their targets.  If this property
is violated, proof output might become very confusing!  For example, a rule
that displays calls to @(see member) as if they were calls to @(see subsetp)
would make proof output very difficult to understand.</p>

<p>We do nothing to enforce this contract.  Hence, a sensible user must ensure
that their use of this table is disciplined.</p>


<h3>Example 1: Mutually Recursive even/odd-p</h3>

<p>This function is just an inefficient check for if a natural number is even
or odd, using a flag-based mutual recursion scheme.</p>

@({
    (defun even/odd-p (flg x)
      (declare (xargs :guard (and (or (eq flg 'even)
                                      (eq flg 'odd))
                                  (natp x))))
      (if (eq flg 'even)
          (if (zp x)
              t
            (even/odd-p 'odd (1- x)))
        (if (zp x)
            nil
          (even/odd-p 'even (1- x)))))
})

<p>Something simple you might want to do with this is 'hide' the flag function
with macros such as the following:</p>

@({
    (defmacro even-p (x)
      `(even/odd-p 'even ,x))

    (defmacro odd-p (x)
      `(even/odd-p 'odd ,x))
})

<p>But of course in proofs you will still see the flag functions.  To hide
these flags, you can call the macro @('add-untranslate-pattern') as
follows:</p>

@({
    (add-untranslate-pattern (even/odd-p 'even ?x) (even-p ?x))
    (add-untranslate-pattern (even/odd-p 'odd ?x)  (odd-p ?x))
})

<p>The effect of these patterns can be seen by submitting the following
commands.  We first disable the type prescription of @('even/odd-p') and its
definition, so that ACL2 will generate terms involving @('even/odd-p').</p>

@({
    (in-theory (disable (:definition even/odd-p)
                        (:type-prescription even/odd-p)))

    (thm (equal (+ (even-p x) (even-p y))
                (+ (odd-p y) (odd-p x))))
})

<p>Some of the proof output generated is now as follows:</p>

@({
    Subgoal *1/2
    (IMPLIES (AND (NOT (EQ 'ODD 'EVEN))
                  (NOT (ZP X))
                  (EQUAL (+ (EVEN-P (+ -1 X)) (EVEN-P Y))
                         (+ (ODD-P (+ -1 X)) (ODD-P Y))))
             (EQUAL (+ (EVEN-P X) (EVEN-P Y))
                    (+ (ODD-P X) (ODD-P Y)))).

    Subgoal *1/2'
    (IMPLIES (AND (NOT (ZP X))
                  (EQUAL (+ (EVEN-P (+ -1 X)) (EVEN-P Y))
                         (+ (ODD-P (+ -1 X)) (ODD-P Y))))
             (EQUAL (+ (EVEN-P X) (EVEN-P Y))
                    (+ (ODD-P X) (ODD-P Y)))).
})

<p>As you can see, @('even/odd-p') is now nicely untranslated into these macro
calls, as we intended, and the flag argument is hidden.</p>


<h3>Example 2: Matt's Challenge</h3>

<p>Matt Kaufmann suggested the following challenge problem, inspired by the
hand-written untranslation routine for the RTL library.  We begin with the
following code:</p>

@({
    (defun foo$ (n $path)
      (cons n $path))

    (defmacro foo (x)
      `(foo$ ,x $path))

    (add-macro-alias foo foo$)
    (in-theory (disable foo))
})

<p>The theorem Matt proposed looking at was the following:</p>

@({
    (thm (equal (list (foo x) (foo$ x $path) (foo$ x other-path))
                (car (cons a b))))
})

<p>With no support for untranslate, this theorem ends up producing the
following goal:</p>

@({
    Goal'
    (EQUAL (LIST (FOO$ X $PATH)
                 (FOO$ X $PATH)
                 (FOO$ X OTHER-PATH))
           A).
})

<p>The RTL untranslator can handle this given the following command:</p>

@({
    (table rtl-tbl 'sigs-btree
           (symbol-alist-to-btree
            (dollar-alist '(foo) nil)))
})

<p>This yields the following, nice goal:</p>

@({
    Goal'
    (EQUAL (LIST (FOO X)
                 (FOO X)
                 (FOO$ X OTHER-PATH))
           A).
})

<p>Matt challenged me to come up with a system that would rewrite only $path.
Using the untranslate pattern table, here is the command:</p>

@({
    (add-untranslate-pattern (foo$ ?n $path) (foo ?n))
})

<p>As you can see, it produces exactly the same output:</p>

@({
    Goal'
    (EQUAL (LIST (FOO X)
                 (FOO X)
                 (FOO$ X OTHER-PATH))
           A).
})


<h3>The Pattern Matching Syntax</h3>

<p>The syntax for these patterns is as follows:</p>

<p>Any quoted constant matches with a quoted constant.  Note that numbers and
so forth must be MANUALLY quoted.</p>

<p>Unquoted symbols behave as follows:</p>

<ul>

<li>If the symbol has no leading @('?') character, then the symbol matches only
with variables of exactly the same name.  For example, if you were using a
stobj named $path, you could use the symbol $path in your pattern and it would
match only with $path.</li>

<li>Symbols beginning with a leading @('?') character are treated as match
variables.  For example, @('?x') in the above patterns behaves as a wildcard
and will match with any term.</li>

</ul>

<p>So, for example, the pattern @('(even/odd-p 'even ?x)') above matches
exactly those terms whose function symbol is @('even/odd-p'), whose first
argument is the quoted constant symbol even, and whose second argument is any
term.</p>

<p>Similarly, the pattern @('(foo$ ?n $path)') matches exactly those terms
whose function symbol is @('foo$'), whose first argument is any term, and
whose second argument is exactly the variable $path.</p>")

(table untranslate-patterns-table 'functions-database nil)
(table untranslate-patterns-table 'constants-database nil)

(defun untranslate-patterns-functions-btree (wrld)
  "Retrieve the untranslate patterns functions btree."
  (declare (xargs :guard (and (plist-worldp wrld)
                              (alistp (table-alist 'untranslate-patterns-table
                                                   wrld)))))
  (cdr (assoc-eq 'functions-database
                 (table-alist 'untranslate-patterns-table wrld))))

(defun untranslate-patterns-constants-alist (wrld)
  "Retrieve the untranslate patterns constants alist."
  (declare (xargs :guard (and (plist-worldp wrld)
                              (alistp (table-alist 'untranslate-patterns-table
                                                   wrld)))))
  (cdr (assoc-eq 'constants-database
                 (table-alist 'untranslate-patterns-table wrld))))

(defmacro add-untranslate-pattern-function (target replacement)
  "Add a new entry to the untranslate patterns functions btree."
  `(table untranslate-patterns-table 'functions-database
          (let* ((function     ',(ffn-symb target))
                 (pat-database (untranslate-patterns-functions-btree world))
                 (curr-subs    (symbol-btree-lookup function pat-database))
                 (new-subs     (acons ',target ',replacement curr-subs)))
            (symbol-btree-update function new-subs pat-database))))

(defmacro add-untranslate-pattern-constant (target replacement)
  "Add a new entry to the untranslate patterns constants alist."
  `(table untranslate-patterns-table 'constants-database
          (let* ((pat-database (untranslate-patterns-constants-alist world)))
            (acons ',target ',replacement pat-database))))

(defsection add-untranslate-pattern
  :parents (untranslate-patterns)
  :short "Add a new pattern to the untranslate patterns table."

  :long "<p>General Form:</p>

@({
    (add-untranslate-pattern target replacement)
})

<p>Examples:</p>

@({
    (add-untranslate-pattern-function '(1 2 3) *myconst*)
    (add-untranslate-pattern-function (f$ ?a ?b mystobj) (f a b))
})

<p>We add a new pattern to the untranslate patterns table.  The target should
be either a quoted constant (which must be fully expanded, it does not get
evaluated), or an unquoted function call.</p>

<p>The first example above changed proof output so that the constant '(1 2 3)
is instead printed as *myconst*.  The second example changes proof output so
that for all @('x,y'), @('(f$ x y mystobj)') is printed as @('(f x y)').  Note
that the printing of @('(f$ x y yourstobj)') will not be altered.</p>"

  (defmacro add-untranslate-pattern (target replacement)
    (if (and (consp target)
             (eq (car target) 'quote))
        `(add-untranslate-pattern-constant ,(cadr target) ,replacement)
      `(add-untranslate-pattern-function ,target ,replacement))))


(defsection optimize-untranslate-patterns
  :parents (untranslate-patterns)
  :short "Optimize the untranslate patterns table."
  :long "<p>Usage:</p>
@({
    (optimize-untranslate-patterns)
})

<p>This macro improves the efficiency of the untranslate-patterns-table by
rebalancing the btree used to internally store patterns for functions and by
cleaning up the alist used to store patterns for constants.  You only need to
call it after adding lots of untranslate patterns, and only if you want to
ensure that untranslation is being done as efficiently as possible.</p>"

  (defmacro optimize-untranslate-patterns ()
    `(progn
       (table untranslate-patterns-table 'functions-database
              (rebalance-symbol-btree
               (untranslate-patterns-functions-btree world)))
       (table untranslate-patterns-table 'constants-database
              (clean-up-alist
               (untranslate-patterns-constants-alist world)
               nil)))))


; UNTRANSLATE EXTENSION -------------------------------------------------------

; We begin by introducing a really simple rewriter.  We define our variables as
; symbols which begin with question marks, e.g., ?x, ?y, etc.

(defun jared-variablep (x)
  (declare (xargs :mode :program))
  (and (symbolp x)
       (let ((name (symbol-name x)))
         (and (not (equal name ""))
              (equal (char name 0) #\?)))))



; We now introduce a simple one-way unification / matching function.  We return
; two values: a boolean flag which indicates if we are successful in finding a
; match, and a list of substitutions of the form (variable . value).
;
; For example:
;
;    (jared-unify-term '(predicate ?x) '(predicate (car a)) nil)
;    ==>
;    (t ((?x . (car a))))

(mutual-recursion

 (defun jared-unify-term (pattern term sublist)
   (declare (xargs :mode :program))
   (if (atom pattern)
       (if (jared-variablep pattern)
           (let ((value (assoc-eq pattern sublist)))
             (if (consp value)
                 (if (equal term (cdr value))
                     (mv t sublist)
                   (mv nil nil))
               (mv t (acons pattern term sublist))))
         (if (equal term pattern)
             (mv t sublist)
           (mv nil nil)))
     (if (or (atom term)
             (not (eq (car term) (car pattern))))
         (mv nil nil)
       (if (eq (car term) 'quote) ; hence also (eq (car pattern) 'quote)
           (if (equal term pattern)
               (mv t sublist)
             (mv nil nil))
         (jared-unify-list (cdr pattern) (cdr term) sublist)))))

 (defun jared-unify-list (pattern-list term-list sublist)
   (declare (xargs :mode :program))
   (if (or (atom term-list)
           (atom pattern-list))
       (if (equal term-list pattern-list) ; same atom
           (mv t sublist)
         (mv nil nil))
     (mv-let (successp new-sublist)
       (jared-unify-term (car pattern-list)
                         (car term-list)
                         sublist)
       (if successp
           (jared-unify-list (cdr pattern-list)
                             (cdr term-list)
                             new-sublist)
         (mv nil nil)))))
 )


; After a list of substitutions has been generated, we typically want to apply
; them to a term.  We recur over the list of substitutions, simply calling
; subst to do our work throughout a term.
;
; For example:
;
;   (jared-substitute '((?x . (car a))) '(not (predicate ?x)))
;   ==>
;   (not (predicate (car a)))

(defun jared-substitute (sublist term)
  (declare (xargs :mode :program))
  (if (endp sublist)
      term
    (let* ((old (car (car sublist)))
           (new (cdr (car sublist)))
           (result (subst new old term)))
      (jared-substitute (cdr sublist) result))))



; We now introduce our actual rewriter.  We take three arguments: pat is the
; pattern to look for throughout the term, e.g., (predicate ?x), repl is the
; replacement to use, e.g., (not (predicate ?x)), and term is the term to match
; the pattern against in order to get the substitutions.
;
; For Example:
;
;   (jared-rewrite1 '(predicate ?x)
;                   '(not (predicate ?x))
;                   '(if (predicate (car x)) t nil))
;   =>
;   (if (not (predicate (car x))) t nil)

(mutual-recursion

 (defun jared-rewrite1 (pat repl term)
   (declare (xargs :mode :program))
   (mv-let (successful sublist)
     (jared-unify-term pat term nil)
     (if successful
         (jared-substitute sublist repl)
       (cond
        ((atom term) term)
        ((eq (car term) 'quote) term)
        ((eq (car term) 'cond)
         (let* ((cond-pairs   (cdr term))
                (tests        (strip-cars cond-pairs))
                (bodies       (strip-cadrs cond-pairs))
                (tests-prime  (jared-rewrite-lst1 pat repl tests))
                (bodies-prime (jared-rewrite-lst1 pat repl bodies)))
           (cons 'cond (pairlis$ tests-prime (pairlis$ bodies-prime nil)))))
        ((member (car term) '(let let*))
         (let* ((names         (strip-cars (second term)))
                (actuals       (strip-cadrs (second term)))
                (actuals-prime (jared-rewrite-lst1 pat repl actuals))
                (length        (length term))
                (nils          (make-list length))
                (ignore        (if (= length 3) nil (third term)))
                (body          (if (= length 3) (third term) (fourth term)))
                (body-prime    (jared-rewrite1 pat repl body))
                (result        (cons (car term)
                                     (cons (pairlis$ names (pairlis$ actuals-prime nils))
                                           (if ignore
                                               (cons ignore (cons body-prime nil))
                                             (cons body-prime nil))))))
           result))
        (t (cons (car term)
                 (jared-rewrite-lst1 pat repl (cdr term))))))))

 (defun jared-rewrite-lst1 (pat repl lst)
   (declare (xargs :mode :program))
   (if (endp lst)
       nil
     (cons (jared-rewrite1 pat repl (car lst))
           (jared-rewrite-lst1 pat repl (cdr lst)))))

 )




; Finally, given that we can apply a rewrite a term with a single replacement,
; we go ahead and extend this notion to multiple replacements.  In other words,
; we walk through a list of substitutions, sequentially rewriting the term
; using each substitution.

(defun jared-rewrite-aux (term subs)
  (declare (xargs :mode :program))
  (if (endp subs)
      term
    (let* ((first-sub (car subs))
           (newterm (jared-rewrite1 (car first-sub)
                                    (cdr first-sub)
                                    term)))
      (jared-rewrite-aux newterm (cdr subs)))))

(defun jared-rewrite (term subs)
  (declare (xargs :mode :program))
  (let ((rw-pass (jared-rewrite-aux term subs)))
    (if (equal rw-pass term)
        term
      (jared-rewrite rw-pass subs))))



; Now we define a really simple untranslate preprocessor that simply returns
; variables, constants, and lambdas in tact, but looks up function applications
; in the database and rewrites them if there is a matching rule.

(defun untranslate-pattern-preprocessor (term world)
  (declare (xargs :mode :program))
  (cond ((or (variablep term)
             (flambda-applicationp term))
         term)
        ((fquotep term)
         (let* ((patterns    (untranslate-patterns-constants-alist world))
                (replacement (assoc-equal (cadr term) patterns)))
           (if replacement
               (cdr replacement)
             term)))
        (t

         (let* ((macro (cdr (assoc (car term) (table-alist 'std::define-macro-fns world)))))

           (if macro ;; Use define's untranslator (borrowed from std/util/define.lisp)

               (let ((macro-args
                      (getprop macro 'macro-args nil 'current-acl2-world world)))
                 (and macro-args
                      (mv-let (ok newargs)
                        (acl2::untrans-macro-args (cdr term) macro-args nil)
                        (and ok
                             (cons macro newargs)))))

             (let* ((patterns (untranslate-patterns-functions-btree world))
                    (subs     (symbol-btree-lookup (ffn-symb term) patterns)))
               (if subs
                   (jared-rewrite term subs)
                 term)))))))


; And all that's left to do is install the new preprocessor!

(table user-defined-functions-table
       'untranslate-preprocess
       'untranslate-pattern-preprocessor)



#|

Here is a little script you can try.

(include-book
 "misc/untranslate-patterns" :dir :system)

(defconst *const* '(a b c d))

(add-untranslate-pattern '(a b c d) *const*)


(defconst *const2* '(1 2 3 4))

(add-untranslate-pattern '(1 2 3 4) *const2*)



(defun even/odd-p (flg x)
  (declare (xargs :guard (and (or (eq flg 'even)
                                  (eq flg 'odd))
                              (natp x))))
  (if (eq flg 'even)
      (if (zp x)
          t
        (even/odd-p 'odd (1- x)))
    (if (zp x)
        nil
      (even/odd-p 'even (1- x)))))

(defmacro even-p (x)
  `(even/odd-p 'even ,x))

(defmacro odd-p (x)
  `(even/odd-p 'odd ,x))

(add-untranslate-pattern (even/odd-p 'even ?x) (even-p ?x))
(add-untranslate-pattern (even/odd-p 'odd ?x) (odd-p ?x))



(defun foo$ (n $path)
  (cons n $path))

(defmacro foo (x)
  `(foo$ ,x $path))

(add-macro-alias foo foo$)

(add-untranslate-pattern (foo$ ?n $path) (foo ?n))



(in-theory (disable (:definition even/odd-p)
                    (:type-prescription even/odd-p)
                    foo))



;; you don't have to do this, but you can if you want.

(optimize-untranslate-patterns)


;; Here's a nonsensical conjecture that will demo the untranslation

(thm
 (implies (and (foo *const*)
               (foo$ *const2* other-path))
          (equal (+ (even-p x) (even-p y))
                 (+ (odd-p y) (odd-p x)))))


;; here's an example of the goal it prints

Subgoal *1/2''
(IMPLIES (AND (NOT (ZP X))
              (EQUAL (+ (EVEN-P Y) (EVEN-P (+ -1 X)))
                     (+ (ODD-P Y) (ODD-P (+ -1 X))))
              (FOO *CONST*)
              (FOO$ *CONST2* OTHER-PATH))
         (EQUAL (+ (EVEN-P X) (EVEN-P Y))
                (+ (ODD-P X) (ODD-P Y))))


|#
