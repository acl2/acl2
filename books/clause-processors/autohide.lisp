; Autohide Hint
; Copyright (C) 2010 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(local (include-book "join-thms"))
(local (include-book "../tools/flag"))
(local (include-book "../tools/do-not"))
(local (include-book "equality"))
(local (do-not generalize fertilize))

(defxdoc autohide
  :parents (hide computed-hints)
  :short "Tell ACL2 to automatically @(see hide) some terms."
  :long "<p>Autohide is a computed hint (see @(see computed-hints)) that scans
your proof goals for any uses of certain functions, and instructs ACL2 to wrap
these calls in @(see hide).  This can be used as a way to tell ACL2 to ignore
certain irrelevant terms so that proofs can be completed faster.</p>

<p>In particular, when I want to speed up a proof, I usually start by using
@(see accumulated-persistence) to see if there are expensive rules that do not
seem to be necessary.  Often there are just a couple of expensive rules that
can be disabled to achieve the bulk of the speedup.</p>

<p>But sometimes the list of rules to disable can get pretty long.  Also, as
the books you are relying upon are updated and extended with new rules, you
might need to go back and additionally disable those rules to keep the proof
fast.  These are cases where autohide may be useful.</p>

<p>Instead of disabling specific rules, autohide tells ACL2 to wrap calls of
certain functions in @(see hide), effectively telling the prover to ignore
those terms.  If you know that, say, the @(see member-equal) terms you are
going to encounter are really irrelevant to what you're trying to prove, then
you might just autohide @('member-equal') instead of trying to disable ten
rules about it.</p>

<h3>Basic Usage</h3>

@({
    (include-book \"clause-processors/autohide\" :dir :system)
    (local (autohide member-equal subsep-equal))
    (defthm my-thm1 ...)
    (defthm my-thm2 ...)
})

<p>The @('(autohide fn1 fn2 ...)') macro expands to a @(see table) event and
just records the names of the functions you want to autohide.</p>

<p>Advice: always localize @('autohide') to avoid inadvertently hiding terms in
other theorems.</p>

<p>Note that @('autohide') is cumulative, so the above is equivalent to:</p>

@({
    (local (autohide member-equal))
    (local (autohide subsetp-equal))
    (defthm my-thm1 ...)
    (defthm my-thm2 ...)
})

<h3>Additional Functions</h3>

<ul>

<li>@('(autohide-summary)') will tell you which functions are currently
     being automatically hidden;</li>

<li>@('(autohide-delete fn1 fn2)') will remove specific functions from
     the autohide table.</li>

<li>@('(autohide-clear)') will clear the table, basically turning off
     autohiding.</li>

</ul>

<p>The autohide hint makes use of a verified @(see clause-processor).  If you
need finer-grained control, e.g., you want to autohide certain functions only
in specific subgoals, you may wish to disable the autohide hint and manually
use the clause processor.</p>")


; -----------------------------------------------------------------------------
;
;                      The Autohide Clause Processor
;
; -----------------------------------------------------------------------------

(mutual-recursion

; WANT-TO-AUTOHIDE: see if a term has any function-calls we want to hide.

 (defund want-to-autohide (x fns)
    (declare (xargs :guard (and (pseudo-termp x)
                               (symbol-listp fns))))
   (cond ((atom x) nil)
         ((eq (car x) 'quote) nil)
         ((eq (car x) 'hide) nil)
         ((member (car x) fns) t)
         (t (want-to-autohide-list (cdr x) fns))))

 (defund want-to-autohide-list (x fns)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (symbol-listp fns))))
   (if (atom x)
       nil
     (or (want-to-autohide (car x) fns)
         (want-to-autohide-list (cdr x) fns)))))


(mutual-recursion

; AUTOHIDE-TERM: wrap any calls of FNS in HIDE.

 (defund autohide-term (x fns)
   (declare (xargs :guard (and (pseudo-termp x)
                               (symbol-listp fns))))
   (cond ((atom x) x)
         ((eq (car x) 'quote) x)
         ((eq (car x) 'hide) x)
         ((member (car x) fns)
          (list 'hide x))
         ;; BOZO should we descend into lambda bodies?
         (t
          (cons (car x) (autohide-term-list (cdr x) fns)))))

 (defund autohide-term-list (x fns)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (symbol-listp fns))))
   (if (atom x)
       x
     (cons (autohide-term (car x) fns)
           (autohide-term-list (cdr x) fns)))))

(local (in-theory (enable pseudo-termp
                          pseudo-term-listp
                          autohide-term
                          autohide-term-list)))

(local (flag::make-flag flag-autohide-term
                        autohide-term
                        :flag-mapping ((autohide-term term)
                                       (autohide-term-list list))))

(local (defthm autohide-term-list-when-atom
         (implies (atom x)
                  (equal (autohide-term-list x fns)
                         x))))

(local (defthm autohide-term-list-of-cons
         (equal (autohide-term-list (cons a x) fns)
                (cons (autohide-term a fns)
                      (autohide-term-list x fns)))))

(local (defthm autohide-term-list-len
         (equal (len (autohide-term-list x fns))
                (len x))))

(local (defun lambda-header-p (x)
         (and (true-listp x)
              (equal (length x) 3)
              (eq (first x) 'lambda)
              (symbol-listp (second x))
              (pseudo-termp (third x)))))

(local (defthm pseudo-termp-of-cons
         (implies (not (eq fn 'quote))
                  (equal (pseudo-termp (cons fn args))
                         (if (symbolp fn)
                             (pseudo-term-listp args)
                           (and (lambda-header-p fn)
                                (pseudo-term-listp args)
                                (equal (len args) (len (second fn)))))))
         :hints(("Goal" :in-theory (enable pseudo-termp)))))

(local (defthm-flag-autohide-term
         (defthm pseudo-termp-of-autohide-term
           (implies (pseudo-termp x)
                    (pseudo-termp (autohide-term x fns)))
           :flag term)
         (defthm pseudo-term-listp-of-autohide-term-list
           (implies (pseudo-term-listp x)
                    (pseudo-term-listp (autohide-term-list x fns)))
           :flag list)))


(defevaluator autohide-ev autohide-ev-lst
  ((if a b c) (hide a)))

(local (defthm autohide-ev-of-disjoin2
         (iff (autohide-ev (disjoin2 t1 t2) env)
              (or (autohide-ev t1 env)
                  (autohide-ev t2 env)))
         :hints(("Goal" :in-theory (enable disjoin2)))))

(local (defthm autohide-ev-of-disjoin
         (iff (autohide-ev (disjoin x) env)
              (or-list (autohide-ev-lst x env)))
         :hints(("Goal" :in-theory (enable disjoin)))))

(local (defthm autohide-ev-of-arbitrary-function
         (implies
          (and (equal (autohide-ev-lst args1 env)
                      (autohide-ev-lst args2 env))
               (symbolp fn)
               (not (equal fn 'quote))
               (syntaxp (term-order args2 args1)))
          (equal (autohide-ev (cons fn args1) env)
                 (autohide-ev (cons fn args2) env)))
         :hints (("goal" :use ((:instance autohide-ev-constraint-0
                                          (x (cons fn args1))
                                          (a env))
                               (:instance autohide-ev-constraint-0
                                          (x (cons fn args2))
                                          (a env)))))))

(local (defthm-flag-autohide-term
         (defthm autohide-term-correct
           (implies (pseudo-termp x)
                    (equal (autohide-ev (autohide-term x fns) env)
                           (autohide-ev x env)))
           :flag term)
         (defthm autohide-term-list-correct
           (implies (pseudo-term-listp x)
                    (equal (autohide-ev-lst (autohide-term-list x fns) env)
                           (autohide-ev-lst x env)))
           :flag list)
         :hints(("Goal"
                 :expand ((:free (a) (hide a)))))))


(defund autohide-cp (clause fns)
  ; The autohide clause processor.
  (declare (xargs :guard (pseudo-term-listp clause)))
  (cond ((not (symbol-listp fns))
         (prog2$ (cw "Warning: autohide-cp invoked with a bad symbol-list.  Not ~
                      hiding any functions.~%~%")
                 (list clause)))
        ;; This check is kind of redundant with the hint, but might be useful
        ;; for manual uses of autohide-cp.
        ((want-to-autohide-list clause fns)
         (list (autohide-term-list clause fns)))
        (t
         (list clause))))

(local (in-theory (enable autohide-cp)))

(defthm autohide-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp env)
                (autohide-ev (conjoin-clauses (autohide-cp clause fns)) env))
           (autohide-ev (disjoin clause) env))
  :rule-classes :clause-processor)




; -----------------------------------------------------------------------------
;
;                      The Autohide Default Hint
;
; -----------------------------------------------------------------------------

(table autohide-table 'fns nil)

(defun autohide-fns (world)
  (declare (xargs :mode :program))
  (cdr (assoc 'fns (table-alist 'autohide-table world))))

(defmacro autohide-summary ()
  `(value-triple
    (let ((fns (autohide-fns (w state))))
      (prog2$
       (if fns
           (cw "Autohides: ~&0.~%" fns)
         (cw "No autohides.~%"))
       :invisible))))

(defmacro autohide (&rest args)
  (declare (xargs :guard (symbol-listp args)))
  `(with-output :off (summary)
                (progn
                  (table autohide-table 'fns
                         (union-equal ',args (autohide-fns world)))
                  (autohide-summary))))

(defmacro autohide-delete (&rest args)
  (declare (xargs :guard (symbol-listp args)))
  `(with-output :off (summary)
                (progn
                  (table autohide-table 'fns
                         (set-difference-equal (autohide-fns world)
                                               ',args))
                  (autohide-summary))))

(defmacro autohide-clear ()
  `(with-output :off (summary)
                (progn
                  (table autohide-table 'fns nil)
                  (autohide-summary))))

(defun autohide-hint (clause world)
  (declare (xargs :mode :program))
  (let ((fns (autohide-fns world)))
    ;; Scanning here seems like a good idea.  I'm never sure how default hints
    ;; interact, but it seems like we don't want to give a hint if we're not
    ;; actually going to modify the clause.
    (if (want-to-autohide-list clause fns)
        `(:clause-processor (:function autohide-cp :hint ',fns))
      nil)))

(add-default-hints! '((autohide-hint clause world)))



#||

; An Example

; CHEAP represents some goal that is easy to prove as long as CHEAP-HYP is
; known.

(defstub cheap (*) => *)
(defstub cheap-hyp (*) => *)
(defaxiom cheap-when-cheap-hyp
  (implies (cheap-hyp x)
           (cheap x)))

; We now make it fairly expensive to rewrite (< 0 (expensive x)).  In practice
; your expensive terms might be applications of something like member-equal,
; subsetp-equal, an arithmetic function, or whatever.
;
; On my computer, (fib 34) takes about a second of computation.  So, this
; syntaxp trick shows us which rule is firing and then causes about a second of
; delay.

(defstub expensive (*) => *)

(defun fib (x)
  (cond ((zp x) 1)
        ((= x 1) 1)
        (t (+ (fib (- x 1)) (fib (- x 2))))))

(defstub foo1 (x) t)
(defstub foo2 (x) t)

(defaxiom expensive-rule-1
  (implies (and (syntaxp (prog2$ (cw "trying rule1 for ~x0~%" x)
                                 (fib 34)))
                (foo1 x))
           (< 0 (expensive x)))
  :rule-classes :rewrite)

(defaxiom expensive-rule-2
  (implies (and (syntaxp (prog2$ (cw "trying rule2 for ~x0~%" x)
                                 (fib 34)))
                (foo2 x))
           (< 0 (expensive x)))
  :rule-classes :linear)

(set-gag-mode nil)

(defthm demo-1
  ;; Proves instantly -- no expensive stuff is in the way
  (implies (cheap-hyp x)
           (cheap x))
  :rule-classes nil)

(defthm demo-2
  ;; Takes 2 seconds because the expensive rules fire
  (implies (and (cheap-hyp x)
                (< 0 (expensive x)))
           (cheap x))
  :rule-classes nil)

(defthm demo-3
  ;; Proves instantly because we disabled both problematic rules.
  (implies (and (cheap-hyp x)
                (< 0 (expensive x)))
           (cheap x))
  :rule-classes nil
  :hints(("Goal" :in-theory (disable expensive-rule-1
                                     expensive-rule-2))))

(encapsulate
  ()
  (local (autohide expensive))

  (defthm demo-4
    ;; Proves instantly because autohide prevents the expensive rules from
    ;; applying.
    (implies (and (cheap-hyp x)
                  (< 0 (expensive x)))
             (cheap x))
    :rule-classes nil))

; Here's the proof-log.
;;
;; ACL2 !>>(DEFTHM DEMO-4
;;                 (IMPLIES (AND (CHEAP-HYP X) (< 0 (EXPENSIVE X)))
;;                          (CHEAP X))
;;                 :RULE-CLASSES NIL)
;;
;; [Note:  A hint was supplied for our processing of the goal above.
;; Thanks!]
;;
;; We now apply the verified :CLAUSE-PROCESSOR function AUTOHIDE-CP to
;; produce one new subgoal.
;;
;; Goal'
;; (IMPLIES (AND (CHEAP-HYP X)
;;               (< 0 (HIDE (EXPENSIVE X))))
;;          (CHEAP X)).
;;
;; By case analysis we reduce the conjecture to
;;
;; Goal''
;; (IMPLIES (AND (CHEAP-HYP X)
;;               (< 0 (HIDE (EXPENSIVE X))))
;;          (CHEAP X)).
;;
;; But simplification reduces this to T, using the :rewrite rule
;; CHEAP-WHEN-CHEAP-HYP.
;;
;; Q.E.D.


(encapsulate
  ()
  (local (autohide <))

  (defthm demo-5
    ;; Proves instantly because autohiding < is just as good as autohiding
    ;; expensive.
    (implies (and (cheap-hyp x)
                  (< 0 (expensive x)))
             (cheap x))
    :rule-classes nil))

||#
