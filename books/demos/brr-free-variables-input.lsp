; Copyright (C) 2021, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The following examples are taken from the documentation topic,
; FREE-VARIABLES-EXAMPLES-REWRITE.  They illustrate ACL2's handling of free
; variables in rewrite rules, as well as user control over how such free
; variables are handled.  See :DOC free-variables for a background discussion.

; Arrange for *standard-co* to be (standard-co state), so that we can see the
; output from brr (via brr-wormhole).
(defttag :brr-free-variables)
(set-raw-mode t)
(defvar *saved-standard-co* *standard-co*)
(progn (setq *standard-co* (standard-co state)) ; avoid output
       t)
(set-raw-mode nil)
(u) ; undo the defttag form

; Set up a starting point for each example.  (It is tempting just to submit the
; command (ubt! 1) at the start of each example, but that would undo some of
; the support for certifying brr-free-variables-book.lisp.)
(deflabel start)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Example 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstub p2 (x y) t) ; introduce unconstrained function

; Get warning because of free variable.  This would be an error if you had
; first executed (set-match-free-error t) in order to force yourself to
; specify :match-free (illustrated later, below).
(defaxiom p2-trans
  (implies (and (p2 x y)
                (p2 y z))
           (p2 x z)))

; Succeeds.
(thm (implies (and (p2 a c)
                   (p2 a b)
                   (p2 c d))
              (p2 a d)))

; The following causes an error because p2-trans is not a rune.
(add-match-free-override :once p2-trans)

; After the following, the rewrite rule p2-trans will only allow one
; attempt per hypothesis to bind free variables.
(add-match-free-override :once (:rewrite p2-trans))

; Now this same theorem fails to be proved.  Here's why.  The
; context for proving (p2 a d) happens to include the hypotheses in
; reverse order.  So when the first hypothesis of p2-trans, namely
; (p2 x y), is relieved, where x is bound to a (as we are attempting
; to rewrite the current literal (p2 a d)), we find (p2 a b) in the
; context before (p2 a c) and hence y is bound to b.  The
; instantiated second hypothesis of p2-trans is thus (p2 b d), and
; the proof fails.  Before the add-match-free-override form above,
; the proof succeeded because the rewriter was allowed to backtrack
; and find the other binding for the first hypothesis of p2-trans,
; namely, y bound to c.  Then the instantiated second hypothesis of
; p2-trans is (p2 c d), which is known to be true in the current
; context.
(thm (implies (and (p2 a c)
                   (p2 a b)
                   (p2 c d))
              (p2 a d)))

; Return to original behavior for binding free variables.
(add-match-free-override :all t)

; Succeeds once again.
(thm (implies (and (p2 a c)
                   (p2 a b)
                   (p2 c d))
              (p2 a d)))

(u) ; undo (add-match-free-override :all t)

; This is an error, since no further arguments should appear after
; :clear.
(add-match-free-override :clear t)

; Return all rules to original behavior for binding free variables,
; regardless of which previous add-match-free-override forms have
; been executed.
(add-match-free-override :clear)

; This succeeds just as it did originally.
(thm (implies (and (p2 a c)
                   (p2 a b)
                   (p2 c d))
              (p2 a d)))

(ubt! 'p2-trans) ; back to the start, except retain the defstub

; Require that :match-free be specified for :linear and :rewrite rules with
; free variables.
(set-match-free-error t)

; Fails because :match-free is missing.
(defaxiom p2-trans
  (implies (and (p2 x y)
                (p2 y z))
           (p2 x z)))

; Fails because :match-free must be followed by :once or :all.
(defaxiom p2-trans
  (implies (and (p2 x y)
                (p2 y z))
           (p2 x z))
  :rule-classes ((:rewrite :match-free nil)))

; Succeeds, this time with no warning at all.
(defaxiom p2-trans
  (implies (and (p2 x y)
                (p2 y z))
           (p2 x z))
  :rule-classes ((:rewrite :match-free :once)))

; Fails because we only bind once (see earlier long comment).
(thm (implies (and (p2 a c)
                   (p2 a b)
                   (p2 c d))
              (p2 a d)))

; Treat p2-trans as though `:match-free :all' had been specified.
(add-match-free-override :all (:rewrite p2-trans))

; Succeeds since more than one binding is allowed for p2-trans.
(thm (implies (and (p2 a c)
                   (p2 a b)
                   (p2 c d))
              (p2 a d)))

(u)
(u)

; Specify that future :linear and :rewrite rules with free variables
; that do not have :match-free specified are treated as though
; `:match-free :once' were specified.
(set-match-free-default :once)

; Succeeds without error since `:match-free' is specified, as described
; above.  But there is a warning, since :match-free is not specified for this
; :rewrite rule.
(defaxiom p2-trans
  (implies (and (p2 x y)
                (p2 y z))
           (p2 x z)))

; Fails since only single bindings are allowed for p2-trans.
(thm (implies (and (p2 a c)
                   (p2 a b)
                   (p2 c d))
              (p2 a d)))

; Treat p2-trans as though `:match-free :all' had been specified.
(add-match-free-override :all t)

; Succeeds.
(thm (implies (and (p2 a c)
                   (p2 a b)
                   (p2 c d))
              (p2 a d)))

; Test searching of ground units, i.e. rewrite rules without variables on the
; left side of the conclusion, for use in relieving hypotheses with free
; variables.  This is a very contrived example.

(ubu! 'start) ; back to the start

(encapsulate
 (((p1 *) => *)
  ((p2 * *) => *)
  ((p3 *) => *)
  ((a) => *)
  ((b) => *))
 (local (defun p1 (x) x))
 (local (defun p2 (x y) (list x y)))
 (local (defun p3 (x) x))
 (local (defun a () 0))
 (local (defun b () 0)))

; Allow default of :match-free :all (form may be omitted).
(set-match-free-error nil)

(defaxiom ax1
  (implies (and (p2 x y)
                (p1 y))
           (p3 x)))

(defaxiom p2-a-b
  (p2 (a) (b)))

(defaxiom p2-a-a
  (p2 (a) (a)))

(defaxiom p1-b
  (p1 (b)))

; Succeeds; see long comment below on next attempt to prove this
; theorem.
(thm (implies (p2 (a) y)
              (p3 (a))))

; Now ax1 will only relieve hypothesis (p2 x y) for one binding of y:
(add-match-free-override :once t)

; Fails when ax1 attempts to rewrite the conclusion to true, because
; the most recent ground unit for hypothesis (p2 x y) with x bound
; to (a) is rule p2-a-a, which binds y to (a).  If more than one ground
; unit could be used then we would backtrack and apply rule p2-a-b,
; which binds y to (b) and hence hypothesis (p1 y) of ax1 is
; relieved by rule p1-b.
(thm (implies (p2 (a) y)
              (p3 (a))))

; Return rules to original :match-free behavior.
(add-match-free-override :clear)

; Succeeds once again.
(thm (implies (p2 (a) y)
              (p3 (a))))

; Just for kicks, change the behavior of a built-in rule irrelevant
; to the proof at hand.
(add-match-free-override :once (:rewrite string<-l-trichotomy))

; Still succeeds.
(thm (implies (p2 (a) y)
              (p3 (a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Example 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ubu! 'start)

(encapsulate
  ((p1 (u x) t)
   (bad (x) t)
   (p2 (x y z) t)
   (bar (x y) t)
   (foo (x y) t)
   (poo (x y) t)
   (prop (u) t))

  (local (defun p1 (u x) (declare (ignore u x)) nil))
  (local (defun bad (x) (declare (ignore x)) nil))
  (local (defun p2 (x y z) (declare (ignore x y z)) nil))
  (local (defun bar (x y) (declare (ignore x y)) nil))
  (local (defun foo (x y) (declare (ignore x y)) nil))
  (local (defun poo (x y) (declare (ignore x y)) nil))
  (local (defun prop (u) (declare (ignore u)) t))

  (defthm foo-poo
    (implies (syntaxp (equal y 'y3))
             (equal (foo x y)
                    (poo x y))))

  (defthm lemma-1
    (implies (and (p1 u x)
                  (bad x)
                  (p2 x y z)
                  (bar x y)
                  (equal x x) ; admittedly silly!
                  (foo x y))
             (prop u))
    :rule-classes ((:rewrite :match-free :all))))

:brr t

; So that brr-free-variables-book.lisp can be certified, we monitor a bit
; differently here from how we monitor in :DOC free-variables-examples-rewrite.
:monitor (:rewrite lemma-1) '(:target :unify-subst :go)

(thm (implies (and (p1 u0 x1)
                   (bad x1)
                   (bad x3)
                   (bar x3 y1)
                   (bar x3 y3)
                   (p1 u0 x2)
                   (p1 u0 x3)
                   (p2 x3 y1 z1)
                   (p2 x3 y3 z1))
              (prop u0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Example 3
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ubu! 'start)

; Define some unary functions.
(defun f (x) (declare (ignore x)) t)
(defun g (x) x)
(defun h (x) x)
(defun k (x) x)

; Prove some simple lemmas.  Note the binding hypothesis in g-rewrite.
(defthm f-k-h
  (f (k (h x))))
(defthm g-rewrite
       (implies (and (equal y (k x)) ; binding hypothesis
                     (f y))
                (equal (g x) y)))

; Restrict to a theory that includes the above lemmas but avoids the above
; definitions.
(in-theory (union-theories (theory 'minimal-theory)
                           '(f-k-h g-rewrite)))

; Prove a theorem.
(thm (equal (g (h a)) (k (h a))))

(ubu! 'start) ; start second sub-example

; Define an equivalence relation.
(defun my-equiv (x y) (equal x y))
(defequiv my-equiv) ; introduces rule MY-EQUIV-IS-AN-EQUIVALENCE

; Define some unary functions
(defun f (x) (declare (ignore x)) t)
(defun g (x) x)
(defun h1 (x) x)
(defun h2 (x) x)

; Prove some simple lemmas.  Note the binding hypothesis in lemma-3.
(defthm lemma-1
  (my-equiv (h1 x) (h2 x)))
(defthm lemma-2
  (f (h2 x)))
(defthm lemma-3
       (implies (and (my-equiv y (double-rewrite x)) ; binding hypothesis
                     (f y))
                (equal (g x) y)))

; Restrict to a theory that includes the above lemmas but avoids the above
; definitions.
(in-theory (union-theories (theory 'minimal-theory)
                           '(lemma-1 lemma-2 lemma-3
                                     my-equiv-is-an-equivalence)))

; Prove a theorem.
(thm (equal (g (h1 a)) (h2 a)))


(in-theory (union-theories (theory 'minimal-theory)
                           '(lemma-1 lemma-2 lemma-3)))

; Proof fails in this case!
(thm (equal (g (h1 a)) (h2 a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; An example from Dave Greve
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ubu! 'start)

; This example, based very closely on one supplied by Dave Greve (but which is
; not in :doc free-variables-examples-rewrite), illustrates that (starting with
; Version 8.4 of ACL2), the brr report for a bind-free hypothesis that returns
; a list of substitutions is similar to the brr report for a hypothesis with
; free variables.

(defstub f (x) nil)
(defstub g (x) nil)

(defaxiom g-rewrite
  (implies (and (f y)
                (syntaxp (not (cw "rewrite trying ~x0~%" y)))
                (equal x y))
           (equal (g x) y)))

(defaxiom g-bind-free
  (implies (and (bind-free `(((y . a)) ((y . b))) (y))
                (syntaxp (not (cw "bind trying ~x0~%" y)))
                (f y)
                (equal x y))
           (equal (g x) y)))

:monitor (:rewrite g-bind-free) '(:target :go)
:monitor (:rewrite g-rewrite) '(:target :go)
:brr t

(thm
 (implies (and (f a)
               (f b))
          (equal (g x) x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :brr-free-variables)
(set-raw-mode t)
(setq *standard-co* *saved-standard-co*)
(set-raw-mode nil)
(u) ; undo the defttag form
