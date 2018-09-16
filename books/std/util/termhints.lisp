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

(defun process-termhint (x)
  (b* (((when (atom x))
        (er hard? 'process-termhint
            "Found an unquoted atom: ~x0 -- don't forget to use ,(hq x) ~
             instead of just ,x. See :xdoc use-termhhint."
            x))
       (f (car x))
       ((when (or (eq f 'quote)
                  (eq f 'hq)))
        (unquote x))
       ((when (eq (car x) 'cons))
        (cons (process-termhint (second x))
              (process-termhint (third x))))
       ((when (eq (car x) 'binary-append))
        (append (process-termhint (second x))
                (process-termhint (third x)))))
    (er hard? 'process-termhint
        "Found an unknown function: ~x0 -- don't forget to use ,(hq x) ~
         instead of just ,x. See :xdoc use-termhhint." x)))

(defxdoc process-termhint
  :parents (use-termhint)
  :short "Processes termhint objects into regular hint objects."
  :long "<p>Essentially this function is an interpreter for terms containing
calls of cons and binary-append, as well as quoted and @(see hq)-quoted
objects, which are both treated the same.  If any other functions or any
variable atoms are present, it produces an error.</p>

<p>This capability is intended to be enough to process backtick expressions
where all the commas are accompanied by hq calls; e.g.:</p>
@({
 (let ((my-a (foo bar baz)))
   (process-termhint `'(:use my-theorem (a ,(hq my-a)))))
=>
 (:USE MY-THEOREM (A (FOO BAR BAZ)))
})")

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
           

(defun use-termhint-find-hint (clause)
  (if (atom clause)
      nil
    (case-match clause
      ((('not ('use-termhint-hyp termhint . &) . &) . &)
       (let ((hint (postprocess-termhint (process-termhint termhint))))
         `(:computed-hint-replacement
           (,@(and hint `(,hint)))
           :clause-processor (remove-hyp-cp clause ',(car clause)))))
      (& (use-termhint-find-hint (cdr clause))))))

(defmacro use-termhint (hint-term)
  `'(:computed-hint-replacement
     ((and stable-under-simplificationp
           (use-termhint-find-hint clause)))
     :use ((:instance use-termhint-hyp-is-true
            (x ,hint-term)))))




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
