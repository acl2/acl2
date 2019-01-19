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

(in-package "ACL2")

(include-book "clause-processors/remove-hyp" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)

(defstub hq (x) nil)

(defxdoc hq
  :parents (use-termhint)
  :short "Stands for Hint-Quote. Used in @(see use-termhint), delimits terms
that go inside hints from the hint boilerplate surrounding them.")

(defun process-termhint (x quotesyms)
  (b* (((when (atom x))
        (er hard? 'process-termhint
            "Found an unquoted atom: ~x0 -- don't forget to use ,(hq x) ~
             instead of just ,x. See :xdoc use-termhhint."
            x))
       (f (car x))
       ((when (member f quotesyms))
        (unquote x))
       ((when (eq (car x) 'cons))
        (cons (process-termhint (second x) quotesyms)
              (process-termhint (third x) quotesyms)))
       ((when (eq (car x) 'binary-append))
        (append (process-termhint (second x) quotesyms)
                (process-termhint (third x) quotesyms))))
    (er hard? 'process-termhint
        "Found an unknown function: ~x0 -- don't forget to use ,(hq x) ~
         instead of just ,x. See :xdoc use-termhhint." x)))

(defxdoc process-termhint
  :parents (use-termhint)
  :short "Processes termhint objects into regular hint objects."
  :long "<p>Essentially this function is an interpreter for terms containing
calls of cons and binary-append, as well as quoted and pseudo-quoted
objects (see below), which are both treated the same.  If any other functions or any
variable atoms are present, it produces an error.</p>

<p>This capability is intended to be enough to process backtick expressions
where all the commas are accompanied by hq (or other pseudoquote) calls; e.g.:</p>
@({
 (let ((my-a (foo bar baz)))
   (process-termhint `'(:use my-theorem (a ,(hq my-a)))))
=>
 (:USE MY-THEOREM (A (FOO BAR BAZ)))
 })

<p>Process-termhint is always called with @('quote') and @('hq') present in
quotesyms, but there may also be others according to the termhint quotesyms
list, which is stored in a table:</p>
@({
 (table termhint 'quotesyms)   ;; show the list of quotesyms
 (cdr (assoc 'quotesyms (table-alist termhint world))) ;; access the list of quotesyms
 (termhint-add-quotesym my-quotesym) ;; add a new quotesym
 })

")

(table termhint nil nil :guard (or (not (eq key 'quotesyms))
                                   (subsetp-eq '(hq quote) val)))
(table termhint 'quotesyms '(hq quote))

(defun termhint-quotesyms (world)
  (cdr (assoc 'quotesyms (table-alist 'termhint world))))

(defmacro termhint-add-quotesym (sym)
  `(table termhint 'quotesyms (cons ',sym (termhint-quotesyms world))))

(set-tau-auto-mode nil)
(encapsulate
  (((use-termhint-hyp *) => *))
  (local (defun use-termhint-hyp (x)
           (declare (ignore x))
           t))
  (defthm use-termhint-hyp-is-true
    (use-termhint-hyp x)
    :rule-classes nil))
(set-tau-auto-mode t)

(defun postprocess-one-termhint (hint)
  (if (and (consp hint) (keywordp (car hint)))
      (kwote hint)
    hint))

(defun postprocess-termhint (hint)
  (case-match hint
    (('termhint-sequence first ('hide second . &)  . &)
     (let ((first (postprocess-one-termhint first)))
       `(termhint-append-hints ,first '(use-termhint ,second))))
    (& (postprocess-one-termhint hint))))
           

(defun use-termhint-find-hint (clause world)
  (if (atom clause)
      nil
    (case-match clause
      ((('not ('use-termhint-hyp termhint . &) . &) . &)
       (let ((hint (postprocess-termhint
                    (process-termhint termhint (termhint-quotesyms world)))))
         `(:computed-hint-replacement
           (,@(and hint `(,hint)))
           :clause-processor (remove-hyp-cp clause ',(car clause)))))
      (& (use-termhint-find-hint (cdr clause) world)))))

(defmacro use-termhint (hint-term)
  `'(:computed-hint-replacement
     ((and stable-under-simplificationp
           (use-termhint-find-hint clause world)))
     :use ((:instance use-termhint-hyp-is-true
            (x ,hint-term)))))

(defmacro use-termhint* (hint-term)
  ;; Same as use-termhint*, but the hint-term is evaluated.
  `(let ((hint-term ,hint-term))
     `(:computed-hint-replacement
       ((and stable-under-simplificationp
             (use-termhint-find-hint clause world)))
       :use ((:instance use-termhint-hyp-is-true
              (x ,hint-term))))))




(defxdoc use-termhint
  :parents (hint-utils)
  :short "Compute hints based on a term that gets simplified along with the rest of the goal."
  :long "<p>When a theory doesn't lend itself well to rewriting, you might just
use a lot of hints to get through a proof.  But this can become brittle and
unwieldy: you might get through the proof by piling on :use hints, but if that
proof later fails it can be very difficult to debug.  An unstructured pile of
hints doesn't give many clues for how the proof is supposed to work and how to
fix it if it breaks.  Use-termhint provides a different way to structure proofs
that require a lot of hints.  Also see @(see termhint-seq) for a way to give
hints in sequence throughout a termhint term.</p>

<h2>Demo</h2>

<p>As a very simple example, suppose that we have axioms ax1 through ax3, and
we want to prove th:</p>

@({
 (defstub p1 (x) t)
 (defstub p2 (x y z) t)
 (defstub p3 (x y) t)
 (defstub p4 (x) t)
 (defstub b (x) t)
 (defstub c (x) t)
 (defstub d (x) t)
 
 (defaxiom t1
   (implies (p1 a)
            (p2 a (b a) (c a))))
 
 (defaxiom t2
   (implies (p2 a b c)
            (p3 a (d c))))
 
 (defaxiom t3
   (implies (p3 a d)
            (p4 a)))
 
 (defthm th
   (implies (p1 a)
            (p4 a)))
})

<p>We could do this using some unstructured :use hints (in this case perhaps
only one would suffice).  But we can be more explicit about how the proof
precedes by using use-termhint, as follows.</p>

<p>First, we write a function that follows the process of the proof and
provides hints at certain endpoints:</p>

@({
 ;; A computed hint to use later -- see below.
 (defun my-use-t3-inst-hint (d)
    `(:use ((:instance t3 (d ,d)))))

 (defun hint-for-th (a)
   (b* ((b (b a))
        (c (c a))
        ;; The first thing that we want to conclude is (p2 a b c) for some b, c,
        ;; namely, the ones given by t1.
        ((unless (p2 a b c))
         ;; The unless here causes a case split.  In one case, we assume (p2 a
         ;; b c).  In the other case, we arrive here, and we return a hint that
         ;; proves the subgoal by proving (p2 a b c).  This hint is
         ;; double-quoted because in general we return the quotation of a
         ;; computed hint expression; in this case, the computed hint we want
         ;; is '(:use t1).
         ''(:use t1))
        ;; Now we can assume (p2 a b c).  Next we want to show (p3 a d) for some d,
        ;; by t2.
        (d (d c))
        ((unless (p3 a d))
         ;; In the case where we're assuming (not (p3 a d)), prove it by using t2.
         ;; Notice the uses of (hq ...) below: these are specially processed by
         ;; use-termhint, so that (hq b) will be replaced by whatever the term
         ;; bound to b has been rewritten to.  This will produce the hint:
         ;;    :use ((:instance t2
         ;;           (b (b a))
         ;;           (c (c a))))
         ;; But notice that we don't have to write out (b a) and (c a); instead we
         ;; use the (hq ...) of variables bound to those terms.
         `'(:use ((:instance t2
                   (b ,(hq b))
                   (c ,(hq c)))))))
     ;; Finally, we have (p3 a d), so we just use t3 to get our conclusion.
     ;; We could use the following:
     ;; `'(:use ((:instance t3 (d ,(hq d)))))
     ;; but instead we'll do this, just to show that you can use arbitrary
     ;; computed hints:
     `(my-use-t3-inst-hint ',(hq d))))
)}

<p>Now, we submit th with the following hints:</p>
@({
 (defthm th
    (implies (p1 a)
             (p4 a))
    :hints ((\"goal\" :in-theory (disable t1 t2 t3))
            (use-termhint (hint-for-th a))))
})
<p>which suffices to prove it.</p>

<h2>Mechanism</h2>

<p>Use-termhint produces a sequence of two computed hints: an initial :use hint
that adds a @('use-termhint-hyp') hypothesis to the goal, and another computed
hint evaluated when stable under simplification, which looks for the simplified
@('use-termhint-hyp') literal and and extracts a hint from that term.</p>

<p>In the above example, the hypothesis added to the goal is
@('(use-termhint-hyp (hint-for-th a))').
This term is processed and simplified like any other.
In particular, the hint-for-th function is opened (because it is an
enabled, non-recursive function) and, because it contains IFs, causes some case
splits.  In each of the three cases, once everything settles down, the
use-termhint-hyp literal remains and contains a term specifying the hint to
give for that case.  This hint is taken care of by the later computed hint,
which strips that hypothesis from the clause and then gives a hint
corresponding to what was in the use-termhint-hyp hypothesis.</p>

<h2>Details</h2>

<p>The @('hq') trick, or something like it, is necessary to allow the hint
object to contain terms that are simplified and beta-reduced by the prover as
well as hint boilerplate that is not.  The function @(see process-termhint) is
used to produce normal hint objects from these; it interprets calls of
@('cons') and @('append') and treats calls of @('hq') like @('quote').</p>

<p>Other quote-like symbols can be added to this list.  In particular, it may
be useful to add symbols that have certain congruences or rewriting properties.
For example, if you want to expand a certain function call and that function
has a congruence on its first argument, you may want to introduce an HQ-like
symbol that has the same congruence:</p>

@({
 (defun my-hq (x) (my-fix x))
 (defcong my-equiv equal (my-hq x) 1)
 (in-theory (disable my-hq (my-hq) (:t my-hq)))
 (termhint-add-quotesym my-hq)

 (defthm ...
   :hints ((use-termhint
            (let ((arg ...))
               `(:expand ((my-fn ,(my-hq arg))))))))
 })
")

(defun termhint-unhide (x) x)
(defthm termhint-unhide-of-hide
  (equal (termhint-unhide (hide x))
         (double-rewrite x))
  :hints (("goal" :expand ((hide x)))))
(in-theory (disable termhint-unhide (termhint-unhide) (:t termhint-unhide)))

(defun termhint-append-hints (prev-hint new-hint)
  (if prev-hint
      (if (eq (car prev-hint) :computed-hint-replacement)
          `(:computed-hint-replacement
            (,@(cadr prev-hint) ,new-hint)
            . ,(cddr prev-hint))
        `(:computed-hint-replacement
          (,new-hint)
          . ,prev-hint))
    nil))

(defmacro termhint-seq (first rest)
  `(b* ((__termhint-seq-hints1 ,first)
        (__termhint-seq-hints2 (hide ,rest)))
     `(termhint-sequence
       ,__termhint-seq-hints1
       ,(hq __termhint-seq-hints2))))

(def-b*-binder termhint-seq
  :decls
  ((declare (xargs :guard (and (consp args) (not (cdr args))
                               (not forms)))
            (ignorable forms)))
  :body
  `(termhint-seq ,(car args) ,rest-expr))

(defxdoc termhint-seq
  :parents (use-termhint)
  :short "Sequence hints within a @(see use-termhint) term."
  :long "<p>Termhint-seq is both a standalone macro and a B* binder that allows
hints to be sequenced within a @(see use-termhint) term.  For example:</p>

@({
 (defun my-sequenced-hints (x)
   (declare (xargs :normalize nil))
   (termhint-seq
     `'(:use ((:instance foo (a ,(hq x)))))
      (if (bar x)
          `'(:use ((:instance foo-when-bar (q ,(hq x)))))
        `'(:expand ((bar ,(hq x)))))))
})

<p>Here, the hint form @('(use-termhint (my-sequenced-hints x))') will (when
stable under simplification) first issue a hint using an instance of @('foo'),
then cause a case split on @('(bar x)') and when stable under simplification
again, use an instance of @('foo-when-bar') in the case where @('(bar x)') is
assumed true and expand @('(bar x)') in the other case.</p>

<p>Note the @(':normalize nil') declaration: this is useful for functions that
use @('termhint-seq'), because it makes use of @('hide') to keep the second set
of hints from causing case splits before the first set of hints is in play;
normalization tends to disrupt this.</p>

<p>A @('b*') binder form of termhint-seq also exists; the following function is
equivalent to the one above:</p>

@({
 (defun my-sequenced-hints (x)
   (declare (xargs :normalize nil))
   (b* (((termhint-seq `'(:use ((:instance foo (a ,(hq x)))))))
        ((when (bar x))
         `'(:use ((:instance foo-when-bar (q ,(hq x)))))))
      `'(:expand ((bar ,(hq x))))))
})

<p>The argument to the @('termhint-seq') binder is the first hint and the rest
of the @('b*') form after that binder is the second hint.</p>")



(set-tau-auto-mode nil)
(encapsulate
  (((mark-clause *) => *))
  (local (defun mark-clause (x)
           (declare (ignore x))
           t))
  (defthm mark-clause-is-true
    (mark-clause x)
    :rule-classes nil))
(set-tau-auto-mode t)

;; :use ((:instance mark-clause-is-true (x 'name-of-clause)))



(defmacro hintcontext (name body)
  `(return-last '(hintcontext) ',name ,body))

(acl2::def-b*-binder hintcontext
  :decls ((declare (xargs :guard (not acl2::forms))
                   (ignore acl2::forms)))
  :body `(hintcontext ,(car acl2::args) ,acl2::rest-expr))

(defmacro hintcontext-bind (bindings body)
  `(return-last '(hintcontext-bind) ',bindings ,body))

(acl2::def-b*-binder hintcontext-bind
  :decls ((declare (xargs :guard (not acl2::forms))
                   (ignore acl2::forms)))
  :body `(hintcontext-bind ,(car acl2::args) ,acl2::rest-expr))

(defun hintcontext-cases-p (cases)
  (Declare (Xargs :guard t))
  (if (atom cases)
      (eq cases nil)
    (and (consp (car cases))
         (or (atom (caar cases))
             (true-listp (caar cases)))
         (consp (cdar cases))
         (not (cddar cases))
         (hintcontext-cases-p (cdr cases)))))

(defun hintcontext-find-case (arg cases)
  (declare (xargs :guard (hintcontext-cases-p cases)))
  (if (atom cases)
      nil
    (if (if (atom (caar cases))
            (equal arg (caar cases))
          (member-equal arg (caar cases)))
        (cadar cases)
      (hintcontext-find-case arg (cdr cases)))))

(defun hintcontext-join (x y)
  (if (and x y)
      `(or ,x ,y)
    (or x y)))

(mutual-recursion
 (defun term-replace-hintcontexts (cases term)
   (Declare (Xargs :mode :program))
   (b* (((when (acl2::variablep term)) nil)
        ((when (acl2::fquotep term)) nil)
        ((cons fn args) term)
        ((when (eq fn 'return-last))
         (cond ((and (equal (first args) ''(hintcontext))
                     (quotep (second args)))
                (hintcontext-join (hintcontext-find-case (unquote (second args)) cases)
                                 (term-replace-hintcontexts cases (third args))))
               ((and (equal (first args) ''(hintcontext-bind))
                     (quotep (second args)))
                `(b* ,(unquote (second args))
                   ,(term-replace-hintcontexts cases (third args))))
               (t (term-replace-hintcontexts cases (third args)))))
        ((when (eq fn 'if))
         (let* ((then (term-replace-hintcontexts cases (second args)))
                (else (term-replace-hintcontexts cases (third args))))
           (and (or then else)
                (list 'if (first args) then else))))
        ((when (atom fn))
         (termlist-replace-hintcontexts cases args))
        (formals (second fn))
        (body (third fn)))
     (hintcontext-join (termlist-replace-hintcontexts cases args)
                      (let ((body (term-replace-hintcontexts cases body)))
                        (and body
                             `((lambda ,formals ,body) . ,args))))))
 (defun termlist-replace-hintcontexts (cases termlist)
   (if (atom termlist)
       nil
     (hintcontext-join (term-replace-hintcontexts cases (car termlist))
                      (termlist-replace-hintcontexts cases (cdr termlist))))))

(defun function-termhint-fn (cases fn world)
  (declare (xargs :mode :program
                  :guard (hintcontext-cases-p cases)))
  (let ((body (acl2::body fn nil world)))
    (term-replace-hintcontexts cases body)))

(defmacro function-termhint (fn &rest cases)
  `(use-termhint*
    (function-termhint-fn ',cases ',fn world)))


(defxdoc hintcontext
  :parents (function-termhint)
  :short "Name a context within a function definition for later use in @(see function-termhint)."
  :long
"
<p>Usage:</p>
@({
 (hintcontext name body)
 })
<p>is logically equivalent to body, and should execute as body with no
overhead, but sets a name for the current context that can be referenced by
@(see function-termhint).</p>

<p>The following @(see b*) binder form is equivalent:</p>
@({
 (b* (((hintcontext name))
      ...)
    ...)
 })")

(defxdoc hintcontext-bind
  :parents (function-termhint)
  :short "Bind variables for use in @(see function-termhint)."
  :long
"
<p>Usage:</p>
@({
 (hintcontext-bind bindings body)
 })
<p>is logically equivalent to body, and should execute as body with no
overhead, but sets up variable bindings that can be used in @(see function-termhint).</p>

<p>The following @(see b*) binder form is equivalent:</p>
@({
 (b* (((hintcontext-bind bindings))
      ...)
    ...)
 })

<p>The main reason to use this is to allow hints to refer to different stages
of a stobj's modifications.  For example:</p>

@({
 (b* (((hintcontxt-bind ((st0 st))))
      (st (update-st-foo x st))
      ((hintcontext-bind ((st1 st))))
      (st (update-st-bar y st))
      ((hintcontext-bind ((st2 st))))
      (st (update-st-baz z st))
      ((hintcontext :after-updates)))
   ...)
 })

<p>If a @(see function-termhint) gives a hint for the @(':after-updates')
context, it will have the following bindings available for use in the hint:</p>
@({
 ((st0 st)
  (st1 (update-st-foo x st))
  (st2 (update-st-bar y (update-st-foo x st)))
  (st  (update-st-baz z (update-st-bar y (update-st-foo x st)))))
 })

")

(defxdoc function-termhint
  :parents (use-termhint)
  :short "Give termhints according to the structure of a function with @(see hintcontext) annotations."
  :long "

<p>Usage (as a computed hint):</p>
@({
 (function-termhint function-name case1 case2 ...)
})
<p>where each case is of one of the following two forms, and each ctxname is the
name given by some @(see hintcontext) annotation in the named function:</p>
@({
 ;; provides termhint at the ctxname hintcontext
 (ctxname termhint)

 ;; provides termhint at the ctxname1 and ctxname2 hintcontexts
 ((ctxname1 ctxname2 ...) termhint)
 })

<h3>Rationale</h3>
<p>Sometimes when using @(see use-termhint) an otherwise sensible hint might
require replicating much of the body of a function.  This utility offers an
alternative.  First, place @(see hintcontext) annotations in the body of the
function in contexts where it makes sense to give a hint.  Then use @(see
function-termhint), which transforms the body of the function to place
user-provided termhint fragments in those contexts.  For example, if @('foo')
is defined as follows:</p>

@({
 (defun foo (x)
   (if (test1 x)
       (let ((y (foo-y x)))
         (if (test2 y)
             (hintcontext :test2-true (foo-ans1 y x))
           (hintcontext :test2-false (foo-ans2 y x))))
     (hintcontext :test1-false (foo-ans3 x))))
  })

<p>then @('function-termhint') can be invoked as follows:</p>

@({
 (defthm foo-prop
     (prop (foo x))
     :hints ((function-termhint foo
              (:test2-true `(:expand ((foo-ans ,(hq y) ,(hq x)))))
              ((:test1-false :test2-false)
               '(:use ((:instance my-lemma (z x))))))))
 })

<p>This is equivalent to:</p>

@({
 (defthm foo-prop
   (prop (foo x))
   :hints ((use-termhint
             (if (test1 x)
                 (let ((y (foo-y x)))
                   (if (test2 y)
                       `(:expand ((foo-ans ,(hq y) ,(hq x)))) ;; :test2-true
                     '(:use ((:instance my-lemma (z x)))))) ;; :test2-false
              '(:use ((:instance my-lemma (z x)))))))) ;; :test1-false
 })

<p>But note that in the latter form, we replicate the IF and LET structure of
the original function, whereas in the former, we only make reference to the
hintcontext labels and bound variables of that function.</p>

<p>An additional utility, @(see hintcontext-bind), can be used to add variable
bindings that don't actually exist in the function but may be used by the
hints.  This is convenient for reasoning about stobjs: each binding of a stobj
in an executable function must shadow all of its previous bindings, but
@('hintcontext-bind') can make previous bindings also available to termhints.</p>

<h3>Operation</h3>

<p>Function-termhint analyzes the (unnormalized) body of the given function and
transforms it into a termhint term by replacing each @('hintcontext')
annotation with the corresponding hint from the user-provided case list.  This
transformation is done by the function @('term-replace-hintcontexts'), which we
describe below.  It uses an operator @('hintcontext-join') which produces the
first non-NIL hint out of its arguments.  In the following description, we call
this joining two potential hints.  The function
@('term-replace-hintcontexts') behaves as follows:</p>

<ul>
<li>If term is a variable or quote, return NIL.</li>

<li>If term is a hintcontext annotation, find the corresponding hint from the
case list and join this with the result of recurring on the body (third
argument).</li>

<li>If term is a hintcontext-bind annotation, create a @(see b*) term whose
bindings are the (unquoted) second argument and whose body is the result of
recurring on the third argument.</li>

<li>If term is any other kind of RETURN-LAST call, return the result of
recurring on the last argument.  (Note: this means we only process the
@(':logic') part of MBE forms.)</li>

<li>If term is an IF, recur on the then and else branches; if either returns a
non-nil result, return @('(if original-test then-result else-result'),
otherwise NIL.</li>

<li>If term is a function call, join the results of recurring on all the
function arguments.</li>

<li>If term is a lambda call, join the results of recurring on all the
arguments as well as, if the recursive call on the lambda body returns a
non-NIL result, the term @('((lambda formals body-result) . original-args)').</li>

</ul>

")
