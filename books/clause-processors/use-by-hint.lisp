

;; This is a computed hint that causes a :by hint to be applied to a subgoal
;; when the first hyp in the clause is (use-by-hint thmname).

;; This can enable clause processors to make use of user-provided,
;; pre-proven ACL2 theorems.  For example, assume a clause processor does
;; something with user-provided theorems and the following theorem is provided
;; to it by the user:
;; (defthm foo-thm (implies (bar x) (equal (foo x) 'baz)))
;; In general, to use the fact provided by this theorem, the clause processor
;; must prove this theorem again.  A quick/easy way to do this is to produce
;; the clause
;; `((not (use-by-hint 'foo-thm))
;;   (implies (bar x) (equal (foo x) 'baz)))
;; If the user (or, say, a computed hint that calls the clause processor)
;; ensures that a (use-by-computed-hint clause) fires when ACL2 attempts to
;; prove this clause, it should then be discharged immediately.

;; See also clause-processors/multi-env-trick for additional help with making
;; clause processors that use user-provided lemmas.

(in-package "ACL2")

(include-book "join-thms")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)

;; USE-BY-HINT is t.  Therefore it can be added as a hyp to any subgoal without
;; affecting its truth value.  It serves to signal use-by-computed-hint to give
;; a particular :by hint.
(defun use-by-hint (x)
  (declare (ignore x))
  t)

(in-theory (disable use-by-hint
                    (use-by-hint)
                    (:type-prescription use-by-hint)))


;; This is a very simple clause processor which simply removes the first
;; literal from the clause.
(defun remove-first-hyp-cp (clause)
  (if (consp clause)
      (list (cdr clause))
    (list clause)))

(defevaluator use-by-hint-ev use-by-hint-ev-lst
  ((if a b c)))

(def-join-thms use-by-hint-ev)

(defthm remove-first-hyp-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (use-by-hint-ev (conjoin-clauses (remove-first-hyp-cp x))
                         a))
           (use-by-hint-ev (disjoin x) a))
  :rule-classes :clause-processor)

;; The computed hint.  Checks to see if the first literal in the clause is a
;; hyp of the form (use-by-hint 'rulename).  If so, first remove that literal
;; using remove-first-hyp-cp, then give a :by hint with that rule.
(defun use-by-computed-hint (clause)
  (declare (xargs :mode :program))
  (case-match clause
    ((('not ('use-by-hint ('quote rule . &) . &) . &) . &)
     `(:computed-hint-replacement
       ('(:by ,rule :do-not '(preprocess simplify)))
       :clause-processor remove-first-hyp-cp))
    (& nil)))


(defun use-these-hints (x)
  (declare (ignore x))
  t)

(in-theory (disable use-these-hints (use-these-hints)
                    (:type-prescription use-these-hints)))


(defun use-these-hints-hint (clause)
  (case-match clause
    ((('not ('use-these-hints ('quote the-hints . &) . &) . &) . &)
     `(:computed-hint-replacement
       ,the-hints
       :clause-processor remove-first-hyp-cp))
    (& nil)))



(defund hq (x) x)
(in-theory (disable (:t hq) (hq)))

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

(defund use-termhint-hyp (x)
  ;; (declare (ignore x))
  (or x t))
(in-theory (disable (:t use-termhint-hyp) (use-termhint-hyp)))

(defun remove-hyp-cp (clause hyp)
  (list (remove-equal hyp clause)))

(defthm disjoin-of-remove-equal
  (implies (not (use-by-hint-ev (disjoin x) a))
           (not (use-by-hint-ev (disjoin (remove hyp x)) a)))
  :hints(("Goal" :in-theory (enable remove))))

(defthm remove-hyp-cp-correct
  (implies (and (pseudo-term-listp x)
                (alistp a)
                (use-by-hint-ev (conjoin-clauses (remove-hyp-cp x hyp))
                                a))
           (use-by-hint-ev (disjoin x) a))
  :rule-classes :clause-processor)

(defun use-termhint-find-hint (clause)
  (if (atom clause)
      nil
    (case-match clause
      ((('not ('use-termhint-hyp termhint . &) . &) . &)
       (let ((hint (process-termhint termhint)))
         `(:computed-hint-replacement
           (,@(and hint `(,hint)))
           :clause-processor (remove-hyp-cp clause ',(car clause)))))
      (& (use-termhint-find-hint (cdr clause))))))

(defmacro use-termhint (hint)
  `'(:computed-hint-replacement
     ((and stable-under-simplificationp
           (use-termhint-find-hint clause)))
     :use ((:instance (:type-prescription use-termhint-hyp)
            (x ,hint)))))




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
     `(termhint-append-hints
       ,__termhint-seq-hints1
       '(use-termhint (termhint-unhide ,(hq __termhint-seq-hints2))))))

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




