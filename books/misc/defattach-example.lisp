; Matt Kaufmann, January 2011

; In this little example we show how defattach may be used to build systems of
; executable programs in which some of the functions are constrain.  Be sure to
; see the final comment, which is really the punch line.

(in-package "ACL2")

; Experienced ACL2 users know that with encapsulate, and without any need for
; defattach, you can deduce theorems about concrete functions from theorems
; about abstract functions, using the following steps.

; (1) Write abstract specifications -- basically, axioms about functions that
;     are shown to hold for some witness functions.

; (2) Prove some theorems about those specification functions.

; (3) Write corresponding concrete definitions.

; (4) Prove that those satisfy the abstract specifications (from (1)).

; (5) Conclude that the theorems (from (2)) hold for the concrete functions
;     (defined in (3)).

; Below we present a standard example of that style of reasoning.  We then show
; how defattach goes beyond this: the idea is still to refine a specification
; function to be to a more concrete definition, but with defattach one can do
; this without changing the function symbol.  That is, the concrete
; strengthening is applied to the original function symbols.

; Here is an outline of the example we present below, using the numbered steps
; shown above.

; (1) Abstract spec:
;     - Specify that ac-fn is associative-commutative (example: +)
;     - Define fold-ac to apply ac-fn to successive elements of list
;       (so for example (fold-ac [1;2;3] r) is (ac 1 (ac 2 (ac 3 r)))).

; (2) Prove that fold-ac(x) = fold-ac(reverse x).

; (3) Concrete definitions:
;     - mult x y = x * y
;     - Define fold-mult in the obvious way.

; (4) Prove that <mult,fold-mult> satisfy the abstract spec for
;     <ac-fn,fold-ac>.

; (5) Conclude that fold-mult(x) = fold-mult(reverse x).

; Here is an example, first without defattach, then with defattach.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;; EXAMPLE WITHOUT DEFATTACH ;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (1) Abstract spec:
;     - Specify that ac-fn is associative-commutative (example: +)
;     - Define fold-ac to apply ac-fn to successive elements of list
;       (so for example (fold-ac [1;2;3] r) is (ac 1 (ac 2 (ac 3 r)))).

(encapsulate
 ((ac-fn (x y) t)) ; introduce ac-fn, a function of two arguments
; Witnessing example:
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

; (2) Prove that fold-ac(x) = fold-ac(reverse x).
; This is theorem fold-ac-reverse, below; the others are lemmas.

(defthm ac-fn-comm2
  (equal (ac-fn x (ac-fn y z))
         (ac-fn y (ac-fn x z)))
  :hints (("Goal"
           :use
           ((:instance ac-fn-assoc (x x) (y y))
            (:instance ac-fn-assoc (x y) (y x)))
           :in-theory (disable ac-fn-assoc))))

(defthm fold-ac-ac-fn
  (equal (fold-ac x (ac-fn a b))
         (ac-fn a (fold-ac x b))))

(defthm fold-ac-revappend
  (equal (fold-ac (revappend x y) root)
         (fold-ac x (fold-ac y root))))

(defthm fold-ac-reverse
  (equal (fold-ac (reverse x) root)
         (fold-ac x root)))

; (3) Concrete definitions:
;     - mult x y = x * y
;     - Define fold-mult in the obvious way.

(defun mult (x y)
  (* (fix x) (fix y)))

(defun fold-mult (x root)
  (if (consp x)
      (mult (car x)
            (fold-mult (cdr x) root))
    root))

; (4) Prove that <mult,fold-mult> satisfy the abstract spec for
;     <ac-fn,fold-ac>.

; (This is proved on the fly, below, with help from an arithmetic
; library.)

(local (include-book "arithmetic/top" :dir :system))

; (5) Conclude that fold-mult(x) = fold-mult(reverse x).

(defthm fold-mult-reverse
  (equal (fold-mult (reverse x) root)
         (fold-mult x root))
  :hints (("Goal"
           :by (:functional-instance
                fold-ac-reverse
                (ac-fn mult)
                (fold-ac fold-mult)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;; EXAMPLE WITH DEFATTACH ;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(verify-guards mult) ; necessary for attachments

(defattach ac-fn mult)

; Example execution using fold-ac (not fold-mult!):
(assert-event (equal (fold-ac '(3 4 5) 1)
                     60))

; Second example:

(defun add (x y)
  (+ (fix x) (fix y)))

(verify-guards add)

(defattach ac-fn add)

; The following example execution really makes our main point: We don't even
; need to define a fold function for add!  We execute with the "abstract"
; function fold-ac, which we think of as "abstract" because it calls the
; encapsulated function ac-fn.  One can imagine more complex examples in which
; a large system of programs contains a few attachments at the leaves of the
; call trees.  In such a case, it's particularly helpful that one can
; instantiate the system to different executable programs without defining
; analogues of the higher-level functions (like fold-ac), thus giving ACL2 some
; ability to mimic a higher-order programming language.

(assert-event (equal (fold-ac '(3 4 5) 100)
                     112))
