; Matt Kaufmann, January 2011 (revised slightly October 2011)
; Distributed with ACL2 as:
; books/misc/defattach-example.lisp

; In this little example we show how defattach may be used
; to build systems of executable programs in which some of
; the functions are constrained.  Be sure to see the final
; comment, which is really the punch line.

(in-package "ACL2")

; Experienced ACL2 users know that by using encapsulate, and
; without any need for defattach, you can deduce theorems
; about concrete functions from theorems about abstract
; functions, using the following steps.

; (1) Write abstract specifications -- basically, axioms
;     about functions that are shown to hold for some
;     witness functions.

; (2) Prove some theorems about those specification
;     functions.

; (3) Write corresponding concrete definitions.

; (4) Prove that those satisfy the abstract specifications
;     (from (1)).

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
;     - Specify that ac-fn is associative-commutative
;       (example: +).
;     - Define fold-ac to apply ac-fn to successive elements
;       of list; for example, (fold-ac '(1 2 3) r) is
;       (ac 1 (ac 2 (ac 3 r))).

; (2) Prove that fold-ac(x) = fold-ac(reverse x).

; (3) Concrete definitions:
;     - Define mult to be multiplication.
;     - Define fold-mult in the obvious way.

; (4) Prove that the pair <mult,fold-mult> satisfies the
;     abstract spec for <ac-fn,fold-ac>.

; (5) Conclude that (fold-mult x) = (fold-mult (reverse x)).

; The second part then takes advantage of the first part,
; resulting in computation using the abstract functions by
; attaching corresponding concrete functions.  We also
; provide a second set of attachments.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;; EXAMPLE WITHOUT DEFATTACH ;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate

; (1) Abstract spec:
;     - Specify that ac-fn is associative-commutative
;       (example: +).
;     - Define fold-ac to apply ac-fn to successive elements
;       of list; for example, (fold-ac '(1 2 3) r) is
;       (ac 1 (ac 2 (ac 3 r))).

 ((ac-fn (x y) t))

; We introduce ac-fn, a function of two arguments.
; Our witnessing example is as follows:

 (local (defun ac-fn (x y)
          (+ x y)))

; Exported specifications:

 (defthm ac-fn-comm
   (equal (ac-fn x y) (ac-fn y x)))
 (defthm ac-fn-assoc
   (equal (ac-fn (ac-fn x y) z)
          (ac-fn x (ac-fn y z)))))

(defun fold-ac (x root)
  (if (consp x)
      (ac-fn (car x)
             (fold-ac (cdr x) root))
    root))

(encapsulate ()

; (2) Prove some theorems about those specification
; functions.

; We prove that fold-ac(x) = fold-ac(reverse x), which is
; theorem fold-ac-reverse, below; the others are lemmas.

 (local (defthm ac-fn-comm2
          (equal (ac-fn x (ac-fn y z))
                 (ac-fn y (ac-fn x z)))
          :hints (("Goal"
                   :use ((:instance ac-fn-assoc (x x) (y y))
                         (:instance ac-fn-assoc (x y) (y x)))
                   :in-theory (disable ac-fn-assoc)))))
 (local (defthm fold-ac-ac-fn
          (equal (fold-ac x (ac-fn a b))
                 (ac-fn a (fold-ac x b)))))
 (local (defthm fold-ac-revappend
          (equal (fold-ac (revappend x y) root)
                 (fold-ac x (fold-ac y root)))))
 (defthm fold-ac-reverse
   (equal (fold-ac (reverse x) root)
          (fold-ac x root))))

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

; (4) Prove that those satisfy the abstract specifications
; (from (1)).

; We prove that the pair <mult,fold-mult> satisfies the
; abstract spec for <ac-fn,fold-ac>.  It is generated as
; part of the proof obligations from the hint below.

; (5) Conclude using functional instantiation that the
;     theorems (from (2)) hold for the concrete functions
;     (defined in (3)).

; We conclude that (fold-mult x) = (fold-mult (reverse x)).

  (equal (fold-mult (reverse x) root)
         (fold-mult x root))
  :hints (("Goal"
           :by (:functional-instance
                fold-ac-reverse
                (ac-fn mult)
                (fold-ac fold-mult)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;; EXAMPLE WITH DEFATTACH ;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-guards ; guard verification needed for defattach
 mult)

; Next we attach the executable function mult to the
; abstract specification function ac-fn.  The proof
; obligations ensure, roughly speaking, that mult satisfies
; the constraints on ac-fn.  In this case the proofs of
; those obligations are skipped because they were already
; proved (and then cached) at the earlier functional
; instantiation (see fold-mult-reverse).

(defattach ac-fn mult)

; Next we do a sample computation using fold-ac
; (interestingly, without calling fold-mult).  The
; foundations guarantees that this computation is taking
; place in a consistent extension of the current theory,
; called the "evaluation theory".  The equality below is a
; theorem of the evaluation theory, but not of the (weaker)
; current theory.

; To see ac-fn transfer control to mult:
; (trace$ ac-fn mult)

(assert-event (equal (fold-ac '(3 4 5) 1)
                     60))

; Note that this equality is NOT a theorem of the current
; session; it's only a theorem if we extend the session by
; "attachment equations" such as the following, to obtain
; the so-called "evaluation history":

; (forall x y) (equal (ac-fn x y) (mult x y))

; Not included because the books/make-event/ directory
; depends on books/misc/:

; (include-book "make-event/eval" :dir :system)
; (must-fail (thm (equal (fold-ac '(3 4 5) 1)
;                        60)))

; Here is a second example, which provides a different
; extension of the current theory to the evaluation theory.

(defun add (x y)
  (+ (fix x) (fix y)))

(verify-guards add)

(defattach ac-fn add)

; The following example execution really makes our main
; point: We don't even need to define a fold function for
; add!  We execute with the "abstract" function fold-ac,
; which we think of as "abstract" because it calls the
; encapsulated function ac-fn.  One can imagine more complex
; examples in which a large system of programs contains a
; few attachments at the leaves of the call trees.  In such
; a case, it's particularly helpful that one can instantiate
; the system to different executable programs without
; defining analogues of the higher-level functions (like
; fold-ac), thus giving ACL2 some ability to mimic a
; higher-order programming language.

; To see ac-fn transfer control to add:
; (trace$ ac-fn add)

(assert-event (equal (fold-ac '(3 4 5) 100)
                     112))
