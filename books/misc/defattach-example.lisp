; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, January, 2011 (revised slightly October, 2011)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See also defattach-bang.lisp for a macro based
; on defattach that does not require guard verification.

; Defattach was introduced in ACL2 Version 4.0 (July, 2010).

; In this little example we show how defattach may be used
; to build systems of executable programs in which some of
; the functions are constrained.  Be sure to see the final
; comment, which is really the punch line.

; For a demo using 800x600 resolution on a 15" laptop:
#||
(set-fmt-soft-right-margin 51 state)
(set-fmt-hard-right-margin 60 state)
||#

(in-package "ACL2")

; Experienced ACL2 users know that by using encapsulate, and
; without any need for defattach, you can deduce theorems
; about concrete functions from theorems about abstract
; functions, using the following steps.

; (1) Write abstract specifications -- basically, axioms
;     about functions that are shown to hold for some
;     witness functions.

; (2) Prove some theorems about the specification functions.

; (3) Write corresponding concrete definitions.

; (4) Prove that the concrete definitions satisfy the
;     abstract specifications.

; (5) Conclude using functional instantiation that the
;     theorems (from (2)) hold for the concrete functions
;     (defined in (3)).

; Below we present a standard example of that style of
; reasoning.  We then show how defattach goes beyond this:
; the idea is still to refine specification functions to
; more concrete definitions, but with defattach one can do
; this in a way that allows evaluation using the original
; function symbols.

; Thus, this file presents an example in two parts:
; traditional functional instantiation without defattach,
; and then evaluation using defattach.

; Here is an outline of the first part, using the numbered
; steps shown above.

; (1) Abstract spec:
;     - Specify that abst is associative-commutative
;       (example: +).
;     - Define fold-abst to apply abst to successive elements
;       of list; for example, (fold-abst '(1 2 3) r) is
;       (abst 1 (abst 2 (abst 3 r))).

; (2) Prove that fold-abst(x) = fold-abst(reverse x).

; (3) Concrete definitions:
;     - Define mult to be multiplication.
;     - Define fold-mult in the obvious way.

; (4) Prove that the pair <mult,fold-mult> satisfies the
;     abstract spec for <abst,fold-abst>.

; (5) Conclude that (fold-mult x) = (fold-mult (reverse x)).

; The second part then takes advantage of the first part,
; resulting in computation using the abstract functions by
; attaching corresponding concrete functions.  We also
; provide a second set of attachments.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;; EXAMPLE WITHOUT DEFATTACH ;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate

; (1) Abstract spec: Specify that abst is
;     associative-commutative (example: +).

 ((abst (x y) t))

; We introduce abst, a function of two arguments.
; Our witnessing example is as follows:

 (local (defun abst (x y)
          (+ x y)))

; Exported specifications:

 (defthm abst-comm
   (equal (abst x y) (abst y x)))
 (defthm abst-assoc
   (equal (abst (abst x y) z)
          (abst x (abst y z)))))

(defun fold-abst (x root)

; Complete abstract spec: define fold-abst to apply abst to
; successive elements of a list; for example,
; (fold-abst '(1 2 3) r) = (abst 1 (abst 2 (abst 3 r))).

  (if (consp x)
      (abst (car x)
            (fold-abst (cdr x) root))
    root))

(encapsulate ()

; (2) Prove some theorems about the specification functions.
; We prove fold-abst-reverse, below; the others are lemmas.

 (local (defthm abst-comm2
          (equal (abst x (abst y z))
                 (abst y (abst x z)))
          :hints (("Goal"
                   :use ((:instance abst-assoc (x x) (y y))
                         (:instance abst-assoc (x y) (y x)))
                   :in-theory (disable abst-assoc)))))
 (local (defthm fold-abst-abst
          (equal (fold-abst x (abst a b))
                 (abst a (fold-abst x b)))))
 (local (defthm fold-abst-revappend
          (equal (fold-abst (revappend x y) root)
                 (fold-abst x (fold-abst y root)))))
 (defthm fold-abst-reverse
   (equal (fold-abst (reverse x) root)
          (fold-abst x root))))

(defun mult (x y)

; (3) Write corresponding concrete definitions.

;     - Define mult to be multiplication.
;     - Below, we define fold-mult in the obvious way.

  (* (fix x) (fix y)))

(defun fold-mult (x root)
  (if (consp x)
      (mult (car x)
            (fold-mult (cdr x) root))
    root))

(local ; included for (4) below
 (include-book "arithmetic/top" :dir :system))

(defthm fold-mult-reverse

; (4) Prove that the concrete definitions satisfy the
;     abstract specifications.

; We prove that the pair <mult,fold-mult> satisfies the
; abstract spec for <abst,fold-abst>.  It is generated as
; part of the proof obligations from the hint below.

; (5) Conclude using functional instantiation that the
;     theorems (from (2)) hold for the concrete functions
;     (defined in (3)).

; We conclude that (fold-mult x) = (fold-mult (reverse x)).

  (equal (fold-mult (reverse x) root)
         (fold-mult x root))
  :hints (("Goal" :by (:functional-instance
                       fold-abst-reverse
                       (abst mult)
                       (fold-abst fold-mult)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; EXAMPLE WITH DEFATTACH ;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#||
(fold-abst '(3 4 5) 100) ; error (undefined function abst)
||#

(verify-guards ; guard verification needed for defattach
 mult)

; Next we attach the executable function mult to the
; abstract specification function abst.  The proof
; obligations ensure, roughly speaking, that mult satisfies
; the constraints on abst.  In this case the proofs of
; those obligations are skipped because they were already
; proved (and then cached) at the earlier functional
; instantiation (see fold-mult-reverse).

(defattach abst mult) ; note cached proof obligations

; Next we do a sample computation using fold-abst
; (interestingly, without calling fold-mult).  The
; foundations guarantees that this computation is taking
; place in a consistent extension of the current theory,
; called the "evaluation theory".  The equality below is a
; theorem of the evaluation theory, but not of the (weaker)
; current theory.

#||
(fold-abst '(3 4 5) 100)
(trace$ abst mult) ; to see abst transfer control to mult
(fold-abst '(3 4 5) 100)
(untrace$)
||#

(assert-event (equal (fold-abst '(3 4 5) 100)
                     6000))

; Note that this equality is NOT a theorem of the current
; session; it's only a theorem if we extend the session by
; "attachment equations" such as the following, to obtain
; the so-called "evaluation history":

; (forall x y) (equal (abst x y) (mult x y))

; Not included because the books/make-event/ directory
; depends on books/misc/:

; (include-book "make-event/eval" :dir :system)
; (must-fail (thm (equal (fold-abst '(3 4 5) 100)
;                        6000)))

; Here is a second example, which provides a different
; extension of the current theory to the evaluation theory.

(defun add (x y)
  (+ (fix x) (fix y)))

(verify-guards add)

(defattach abst add) ; note constraint proof this time

; The following example execution really makes our main
; point: We don't even need to define a fold function for
; add!  We execute with the "abstract" function fold-abst,
; which we think of as "abstract" because it calls the
; encapsulated function abst.  One can imagine more complex
; examples in which a large system of programs contains a
; few attachments at the leaves of the call trees.  In such
; a case, it's particularly helpful that one can instantiate
; the system to different executable programs without
; defining analogues of the higher-level functions (like
; fold-abst), thus giving ACL2 some ability to mimic a
; higher-order programming language.

; To see abst transfer control to add:
; (trace$ abst add)

(assert-event (equal (fold-abst '(3 4 5) 100)
                     112))

; Here are some forms to run at the end of a demo:
#||
(defattach abst mult) ; note cached proof obligations

(fold-abst '(3 4 5) 100)

(thm

; This FAILS!  ACL2 does not use attachments for
; evaluation of ground terms during rewriting, because
; it is proving theorems about the current ACL2 world,
; not the so-called "evaluation theory" in which we know
; (equal (abst x y) (mult x y)).

 (equal (fold-abst '(3 4 5) 100)
        6000))
||#
