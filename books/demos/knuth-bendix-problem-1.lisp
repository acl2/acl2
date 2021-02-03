; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; An example illustrating the use GL to prove unbounded theorems

; In :doc TIPS we see the following, which points to the present file.

;   Also assure that subexpressions on the left hand
;   side of a rewrite rule are in simplified form; see community-books
;   example books/demos/knuth-bendix-problem-1.lisp.

; The following from :doc INTRODUCTION-TO-REWRITE-RULES-PART-2 also describes
; the situation discussed in this file.

;   Choose a Left-Hand Side Already in Simplest Form:

; I've inserted comments below that are intended to make this all clear.

(in-package "ACL2")

; Introduce three functions and two properties of them.

(defun foo (x)
  x)

(defun bar (x)
  x)

(defun h1 (x)
  x)

(defthm rule-1
  (equal (h1 (foo (bar x)))
         x))

(defthm rule-2
  (equal (foo (bar x))
         x))

(include-book "std/testing/must-fail" :dir :system)

(must-fail

; The following theorem illustrates the "Knuth-Bendix problem".  Since
; rewriting is inside-out, rule-2 simplifies the term (foo (bar a)) to a.  So
; we are left with the simplification checkpoint (equal (h1 a) a), and rule-1
; is useless in simplifying the call of h1 because of the disappearance of the
; argument (foo (bar a)) of h1.

 (thm (equal (h1 (foo (bar a)))
             (foo (bar a)))
      :hints (("Goal"
               :in-theory
               (union-theories '(rule-1 rule-2)
                               (theory 'ground-zero))))))

(must-fail

; If we enable only rule-1, then of course the call of h1 is simplified using
; rule-1, but the second argument of EQUAL is not simplified (because rule-2 is
; disabled).

 (thm (equal (h1 (foo (bar a)))
             (foo (bar a)))
      :hints (("Goal"
               :in-theory
               (union-theories '(rule-1)
                               (theory 'ground-zero))))))

(must-fail

; If we enable only rule-2, then we're back to the behavior of the first THM
; attempt, since in both cases, rule-1 does nothing.

 (thm (equal (h1 (foo (bar a)))
             (foo (bar a)))
      :hints (("Goal"
               :in-theory
               (union-theories '(rule-2)
                               (theory 'ground-zero))))))

; WARNING: The following proof succeeds but is not recommended.  The necessary
; use of subgoal hints for this solution (necessary, as shown above) suggests a
; problem with our set of rules: the left-hand side of rewrite rule rule-1 is
; not in simplest ("normal") form, because it can be simplified using rule-2.
; We succeed here only because we first apply rule-1 to simplify the call of h1
; and then, later, we apply rule-2 to simplify the second argument of EQUAL,
; that is, (foo (bar a)).  What we want instead (see below) is a set of rewrite
; rules whose left-hand sides are all in simplest form, to avoid this sort of
; subgoal-level micromanagement (which can get quite complex in large proofs).

(defthm ugly-success
  (equal (h1 (foo (bar a)))
         (foo (bar a)))
  :hints (("Goal"
           :in-theory
           (union-theories '(rule-1)
                           (theory 'ground-zero)))
          ("Goal'"
           :in-theory
           (union-theories '(rule-2)
                           (theory 'ground-zero))))
  :rule-classes nil)

; So here is a better solution (that is, better than using subgoal-level
; hints).  First, we fix rule-1 so that its left-hand side has been simplified
; using rule-2.

(defthm rule-1-better
  (equal (h1 x)
         x))

; Now we disable rule-1 so that we only need to think about its "better"
; version.  Since we are specifying user-defined rules explicitly (see the call
; of union-theories below), we don't actually need to do this here.  But in
; general, one may wish to do this kind of disable so that the current theorey
; (set of enabled rule) is nice.

(in-theory (disable rule-1))

; Finally, our original THM succeeds, using rule-1-better in place of rule-1.

(defthm pretty-success
  (equal (h1 (foo (bar a)))
         (foo (bar a)))
  :hints (("Goal"
           :in-theory
           (union-theories '(rule-1-better rule-2)
                           (theory 'ground-zero))))
  :rule-classes nil)
