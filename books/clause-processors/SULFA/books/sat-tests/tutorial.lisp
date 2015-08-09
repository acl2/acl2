
;; A tutorial of the SULFA clause processor system.

;; We use the term Subclass of Unrollable List Formulas in
;; ACL2 (SULFA) to refer to the decidable subclass of
;; ACL2 formulas understood by our clause processor.  We
;; also refer to the clause processor itself as SULFA, though
;; it is actually defined as an ACL2 function named "sat".

(in-package "ACL2")

;; To use our system, first we need to include the clause
;; processor book.  It requires two ttags "sat" and "sat-cl",
;; representing the system call to the SAT solver and the
;; SULFA-SAT clause processor respectively.

(include-book "../clause-processors/sat-clause-processor" :ttags (sat sat-cl))

;; The point of the SULFA-SAT clause processor is to
;; use SAT solvers to verify ACL2 formulas automatically.

;; First, let's prove a propositional formula

(defthm prop-form-1
  (or (and a b)
      (and (not a) b)
      (not b))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; If we give an invalid SULFA formula, then
;; the clause processor produces a counter-example.

#|
;; For example

(defthm prop-invalid
  (or (and a b)
      (and (not a) b)
      b)
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; Produces the following output (using the zChaff SAT solver),
;; which correctly identives a=nil, b=nil as a counter-example.

[Note:  A hint was supplied for our processing of the goal above.
Thanks!]
[SGC for 0 RELOCATABLE-BLOCKS pages..(77546 writable)..(T=2).GC finished]
The expression is in our decidable subclass of ACL2 formulas (SULFA).
Calling SAT solver.  Num-vars: 7, Num-clauses: 19
Time spent by SAT solver: 0
[SGC for 0 RELOCATABLE-BLOCKS pages..(77546 writable)..(T=12).GC finished]
Generating counter-example:
The following counter example was generated:
B: NIL
A: NIL
Checking counter-example.
The formula evaluated to false, so the counter example is real.


ACL2 Error in ( DEFTHM PROP-INVALID ...):  Error in clause-processor
hint:

  The SAT-based procedure failed to verify the formula



Summary
Form:  ( DEFTHM PROP-INVALID ...)
Rules: NIL
Warnings:  None
Time:  0.16 seconds (prove: 0.16, print: 0.00, other: 0.00)

******** FAILED ********  See :DOC failure  ******** FAILED ********
ACL2 !>

|# ;|

;; Any function that breaks down into "if" functions
;; can be converted to SAT.

(defthm prop-form-2
  (implies (and (iff a b)
                (iff b c))
           (iff a c))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; We also support equality (though it isn't as efficient as I'd like).

(defthm prop-form-3
  (implies (and (equal a b)
                (equal b c))
           (equal a c))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; And we support the list primitives, car, cdr, cons, and consp

;; For example, here's a theorem that might not be intuitively
;; obvious:
(defthm prop-form-4
  (implies (and (not (equal (car a) 'nil))
                (equal (car a) (car b))
                (equal (cdr a) (cdr b))
                (equal (car b) (car c))
                (equal (cdr b) (cdr c)))
           (equal a c))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

#|
;; Note that the first hypothesis is necessary, as
;; the clause processor correctly identifies the
;; counter-example a='nil, b='(nil), c='(nil) in
;; the theorem below

(defthm prop-invalid
  (implies (and (equal (car a) (car b))
                (equal (cdr a) (cdr b))
                (equal (car b) (car c))
                (equal (cdr b) (cdr c)))
           (equal a c))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

[Note:  A hint was supplied for our processing of the goal above.
Thanks!]
[SGC for 0 RELOCATABLE-BLOCKS pages..(88160 writable)..(T=7).GC finished]
The expression is in our decidable subclass of ACL2 formulas (SULFA).
Calling SAT solver.  Num-vars: 19, Num-clauses: 52
Time spent by SAT solver: 0
Generating counter-example:
The following counter example was generated:
C: (NIL)
B: (NIL)
A: NIL
Checking counter-example.
The formula evaluated to false, so the counter example is real.


ACL2 Error in ( DEFTHM PROP-INVALID ...):  Error in clause-processor
hint:

  The SAT-based procedure failed to verify the formula



Summary
Form:  ( DEFTHM PROP-INVALID ...)
Rules: NIL
Warnings:  None
Time:  0.10 seconds (prove: 0.10, print: 0.00, other: 0.00)

******** FAILED ********  See :DOC failure  ******** FAILED ********
ACL2 !>

|# ;|

;; We call the functions equal, if, car, cdr, cons, and consp the
;; SULFA primitives.

;; If you try to prove most theorems about other core ACL2 primitives,
;; you get a message saying that the formula is not in SULFA.

#|

;; For example:
(defthm +-failure
  (equal (+ a b) (+ b a))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; Produces

[Note:  A hint was supplied for our processing of the goal above.
Thanks!]
[SGC for 0 RELOCATABLE-BLOCKS pages..(77551 writable)..(T=5).GC finished]


ACL2 Error in ( DEFTHM |+-FAILURE| ...):  Error in clause-processor
hint:

  ERROR: This formula is not in our decidable subclass (SULFA)



Summary
Form:  ( DEFTHM |+-FAILURE| ...)
Rules: NIL
Warnings:  None
Time:  0.06 seconds (prove: 0.06, print: 0.00, other: 0.00)

******** FAILED ********  See :DOC failure  ******** FAILED ********
ACL2 !>
|# ;|

;; However, we also can handle uninterpreted functions.
;; For example, if we create a symbol "f" using defstub

(defstub f (*) => *)

;; We can prove:

(defthm uninterpreted-prop-1
  (implies (and (equal (f x) (f y))
                (equal (f y) (f z))
                (equal a z))
           (equal (f x) (f a)))
  :hints (("Goal" :clause-processor
           (:function
            sat
            :hint
            '(:check-counter-example nil))))
  :rule-classes nil)
;; (the check-counter-example=nil hint tells the clause processor
;;  not to execute the any counter-example found, since the formula
;;  isn't executable).

;; And we support "treating a function as if it were uninterpreted".
;; For example, in the property below we treat "+" and "<" as
;; uninterpreted:

(defthm uninterpreted-prop-2
  (implies (and (equal x a)
                (equal y b)
                (equal (+ a 4) 25)
                (< x y))
           (< a b))
  :hints (("Goal" :clause-processor
           (:function
            sat
            :hint
            '(:uninterpreted-functions (< binary-+)))))
  :rule-classes nil)

;; Note that we can't treat macros as uninterpreted functions,
;; so we treat "binary-+" as uninterpreted, rather than +.

#|
;; Of course, if we try to prove something about an uninterpreted
;; function, we are limited to proving that it is true for all functions.

;; Therefore, the following property is not proven

(defthm uninterpreted-failure
  (equal (+ a b) (+ b c))
  :hints (("Goal" :clause-processor
           (:function
            sat
            :hint
            '(:uninterpreted-functions (binary-+)))))
  :rule-classes nil)

;; producing the following output:
[Note:  A hint was supplied for our processing of the goal above.
Thanks!]
[SGC for 0 RELOCATABLE-BLOCKS pages..(77551 writable)..(T=2).GC finished]
The expression is in our decidable subclass of ACL2 formulas (SULFA).
Calling SAT solver.  Num-vars: 6, Num-clauses: 8
Time spent by SAT solver: 0
[SGC for 0 RELOCATABLE-BLOCKS pages..(77551 writable)..(T=13).GC finished]
Generating counter-example:
The following counter example was generated:
C: NIL
B: T
A: NIL
(BINARY-+ NIL T): NIL
(BINARY-+ T NIL): T
Checking counter-example.
The formula evaluated to true, so the counter example is SPURIOUS.


ACL2 Error in ( DEFTHM UNINTERPRETED-FAILURE ...):  Error in clause-
processor hint:

  The SAT-based procedure failed to verify the formula



Summary
Form:  ( DEFTHM UNINTERPRETED-FAILURE ...)
Rules: NIL
Warnings:  None
Time:  0.17 seconds (prove: 0.17, print: 0.00, other: 0.00)

******** FAILED ********  See :DOC failure  ******** FAILED ********
ACL2 !>

|# ;|

;; The power of SULFA though, really comes from user-defined functions.

;; And now we can prove theorems about xor, using the clause processor:

(defthm xor-thm-1
  (iff (xor a0 (xor a1 (xor a2 a3)))
       (xor a3 (xor a2 (xor a1 a0))))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; We can also define new functions from xor and prove theorems about them:

(defun xor3 (a b c) (xor a (xor b c)))

(defthm xor-thm-2
  (iff (xor3 a b c)
       (xor3 c a b))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; We also support the restricted application of functions defined
;; using arbitrary executable functions.

;; For example, consider the following function foo:

(defun foo (a b)
  (if (zp a)
      b
    (cdr b)))

;; Because "zp" only is used on the first argument, we allow
;; applications of "foo" as long as the first argument evaluates
;; to a constant.

(defthm foo-prop-1
  (implies (not (equal b 'nil))
           (not (equal (cdr (foo (+ 7 6) b)) b)))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; We call the first argument of foo a "ground formal" because
;; it must be grounded in any SULFA formula.

#|
;; To lookup the ground formals of a function, you can use:
(sat-ground-formals 'foo $sat state)

;; Which returns the error quadruple:
(NIL (T NIL) <$sat> <state>)
;; where the second argument is a list of Boolean representing
;; whether the corresponding formal of 'foo is a ground formal.

;; For example, to see that all arguments of 'binary-+
;; must be grounded
(sat-ground-formals 'binary-+ $sat state)
;; returns
(NIL (T T) <$sat> <state>)

;; to see that no arguments of xor3 must be grounded:
(sat-ground-formals 'xor3 $sat state)
;; returns
(NIL (NIL NIL NIL) <$sat> <state>)

;; Note: that these results are always relative to the
;; the last uninterpreted-functions list given to the
;; clause processor.  If we attempt to prove:

(defthm uninterpreted-failure
  (equal (+ a b) (+ b c))
  :hints (("Goal" :clause-processor
           (:function
            sat
            :hint
            '(:uninterpreted-functions (binary-+)))))
  :rule-classes nil)

;; Then
(sat-ground-formals 'binary-+ $sat state)
;; returns
(NIL (NIL NIL) <$sat> <state>)
;; Since we're treating 'binary-+ as an uninterpreted function.
;; (once you call the clause processor with a new uninterpreted
;;  function list, the ground formals will reset).
|# ;|

;; SULFA also contains restricted applications of recursively
;; defined functions.  We use the notion of ground formals to
;; force applications of recursive functions to be unrollable.

;; For example, the following defined an n bit, bit-vector adder

(defun maj3 (x y z)
  (if x (or y z)
    (and y z)))

;; Returns a n+1 length sum of the first
;; n bits of a and b (plus the carry).
(defun v-adder (n c a b)
  (if (zp n)
      (list c)
    (cons (xor3 c (car a) (car b))
          (v-adder (1- n)
                   (maj3 c (car a) (car b))
                   (cdr a) (cdr b)))))

#|
;; The first formal of v-adder must be a ground formal,
;; both because of its use in (zp n), and its use in
;; the recursive measure of v-adder.

(sat-ground-formals 'v-adder $sat state)
;; =>
(NIL (T NIL NIL NIL) <$sat> <state>)

;; Thus, the "commutativity of an 8 bit v-adder" is in SULFA

(defthm 8-v-adder-commute
  (equal (v-adder 8 nil a b)
         (v-adder 8 nil b a))
    :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; But the above property isn't a theorem for untyped domains, and
;; SULFA finds a counter-example:

[Note:  A hint was supplied for our processing of the goal above.
Thanks!]
[SGC for 0 RELOCATABLE-BLOCKS pages..(87209 writable)..(T=6).GC finished]
The expression is in our decidable subclass of ACL2 formulas (SULFA).
Calling SAT solver.  Num-vars: 84, Num-clauses: 320
Time spent by SAT solver: 0
Generating counter-example:
The following counter example was generated:
B: (NIL NIL T T T T NIL SAT::X0)
A: (NIL T NIL T T T NIL T)
Checking counter-example.
The formula evaluated to false, so the counter example is real.


ACL2 Error in ( DEFTHM V-ADDER-COMMUTE ...):  Error in clause-processor
hint:

  The SAT-based procedure failed to verify the formula



Summary
Form:  ( DEFTHM V-ADDER-COMMUTE ...)
Rules: NIL
Warnings:  None
Time:  0.09 seconds (prove: 0.09, print: 0.00, other: 0.00)

******** FAILED ********  See :DOC failure  ******** FAILED ********
ACL2 !>

|# ;|

;; One way to fix this is to define an n bit, bit-vector predicate:

(defun n-bvp (n x)
  (cond
   ((zp n)
    t)
   ((booleanp (car x))
    (n-bvp (1- n) (cdr x)))
   (t
    nil)))

;; Now we can prove the theorem over bit vectors:

(defthm 8-v-adder-commute
  (implies
   (and (n-bvp 8 a)
        (n-bvp 8 b))
   (equal (v-adder 8 nil a b)
          (v-adder 8 nil b a)))
   :hints (("Goal" :clause-processor (:function sat :hint nil)))
   :rule-classes nil)

;; You might ask how big a commute property can we prove with SULFA.

;; The following 1024 bit theorem goes through pretty easily
;; (27 seconds with zChaff on my machine):
(defthm 1024-v-adder-commute
  (implies
   (and (n-bvp 1024 a)
        (n-bvp 1024 b))
   (equal (v-adder 1024 nil a b)
          (v-adder 1024 nil b a)))
   :hints (("Goal" :clause-processor (:function sat :hint nil)))
   :rule-classes nil)

;; In order to get much bigger with our system, you would want to switch to
;; a bit-vector equality operation, rather than using the n-bit Boolean predicate
;; (remember that equal isn't that efficient) and use a tree representation
;; for bit vectors rather than a list representation (when trees
;; get over a thousand elements deep, like the lists in this bit-vector
;; representation, it puts significant pressure on the conversion algorithm).

;; Another efficiency note, while we're on the subject, is to remember
;; that your functions are unrolled.  So don't duplicate recursive applications
;; unnecessarily.

(defun bar (n x ans)
  (cond
   ((zp n)
    ans)
   (t
    (or (bar (1- n) (cdr x) (or (equal (car x) 0) ans))
        (bar (1- n) (cdr x) (or (equal (car x) 1) ans))))))

(defthm bar-prop
  (implies (equal (nth 5 x) 1)
           (bar 10 x nil))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; In the property above, the application of "bar" explodes during
;; unrolling.  Thus, an n=10 is about as big as we can get.

;; However, if we a version of "bar" with only one recursive call, it
;; does not explode:

(defun bar-better (n x ans)
  (cond
   ((zp n)
    ans)
   (t
    (bar-better (1- n)
                (cdr x)
                (or (equal (car x) 0)
                    (equal (car x) 1)
                    ans)))))

(defthm bar-better-prop
  (implies (equal (nth 50 x) 1)
           (bar-better 100 x nil))
  :hints (("Goal" :clause-processor (:function sat :hint nil)))
  :rule-classes nil)

;; For a more fun example, we can load in our model of the
;; Sudoku puzzle:

(include-book "sudoku" :ttags (sat sat-cl))

;; We've modeled the puzzle constraints using ACL2.
;; Thus, we can represent a puzzle as an ACL2 constant:

(defconst *puzzle*
  '((X X 6 7 X X 4 X X)
    (9 8 X X X X 3 X X)
    (X X X 8 2 X X X X)
    (X X X 6 X 2 5 X X)
    (3 X X X 5 X X X 6)
    (X X 1 4 X 8 X X X)
    (X X X X 1 5 X X X)
    (X X 2 X X X X 7 8)
    (X X 3 X X 7 1 X X)))

#|
;; Now if we try to prove the puzzle has no solution,
;; our clause processor produces a solution as a counter-example:

(thm
 (implies (satisfies-constraintsp *puzzle* x)
          (not (good-solutionp x)))
 :hints (("Goal" :clause-processor (:function sat :hint nil))))

;; Here's the output

[SGC for 4763 FIXNUM pages..(97600 writable)..(T=7).GC finished]
[SGC for 4763 FIXNUM pages..(97600 writable)..(T=7).GC finished]
Calling SAT solver.  Num-vars: 8123, Num-clauses: 393829
Time spent by SAT solver: 0.084005
Generating counter-example:
The following counter example was generated:
X:
((2 1 6 7 9 3 4 8 5)
 (9 8 4 5 6 1 3 2 7)
 (7 3 5 8 2 4 6 1 9)
 (8 4 9 6 7 2 5 3 1)
 (3 2 7 1 5 9 8 4 6)
 (5 6 1 4 3 8 7 9 2)
 (4 7 8 9 1 5 2 6 3)
 (1 5 2 3 4 6 9 7 8)
 (6 9 3 2 8 7 1 5 4))

Checking counter-example.
The formula evaluated to false, so the counter example is real.


ACL2 Error in ( THM ...):  Error in clause-processor hint:

  The SAT-based procedure failed to verify the formula



Summary
Form:  ( THM ...)
Rules: NIL
Warnings:  None
Time:  2.98 seconds (prove: 2.98, print: 0.00, other: 0.00)

******** FAILED ********  See :DOC failure  ******** FAILED ********
ACL2 !>

|# ;|

