; Correctness of Less Than

; Problem: Define an M1 program to compute whether natural number x is less than
; natural number y.  Indicate true with 1 and false with 0.

; Design Plan: I will count x and y both down by 1 and stop when either reaches
; 0.  If y reaches 0 first (or at the same time), x < y was false.  If x
; reaches 0 before y, x < y was true.

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; (1) Write your specification, i.e., define the expected inputs and the
; desired output, theta.

(defun ok-inputs (x y)
  (and (natp x)
       (natp y)))

(defun theta (x y)
  (if (< x y) 1 0))

; (2) Write your algorithm.  This will consist of a tail-recursive helper
; function and a wrapper, fn.

; Note:  In this case, the helper and the top-level fn are the same.  We
; don't need both, but we'll stick with the template.

(defun helper (x y)
  (cond ((zp y) 0)
        ((zp x) 1)
        (t (helper (- x 1) (- y 1)))))

(defun fn (x y) (helper x y))

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.

; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n, m, a, and rest and fn calls helper initializing a to 0 and rest to nil,
; your helper theorem must be about (helper n m a rest), not just about the
; special case (helper n m 0 nil).

(defthm helper-is-theta
  (implies (and (natp x)
                (natp y))
           (equal (helper x y)
                  (theta x y))))

(defthm fn-is-theta
  (implies (ok-inputs x y)
           (equal (fn x y)
                  (theta x y))))

; Disable these two lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper-is-theta fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.

(defconst *pi*
  '((iload 1)   ;  0   lessp-loop:          -- the code for lessp
    (ifeq 12)   ;  1   if y=0, goto false
    (iload 0)   ;  2
    (ifeq 12)   ;  3   if x=0, goto to true
    (iload 0)   ;  4
    (iconst 1)  ;  5
    (isub)      ;  6
    (istore 0)  ;  7   x = x-1
    (iload 1)   ;  8
    (iconst 1)  ;  9
    (isub)      ; 10
    (istore 1)  ; 11   y = y-1
    (goto -12)  ; 12   goto lessp-loop
    (iconst 0)  ; 13   lessp is false
    (halt)      ; 14
    (iconst 1)  ; 15   lessp is true
    (halt)      ; 16   return a
    ))

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun loop-clk (x y)
  (if (zp y)
      4
      (if (zp x)
          5
          (clk+ 13
                (loop-clk (- x 1) (- y 1))))))

(defun clk (x y)
  (loop-clk x y))

; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Important Note: Your lemmas about your loops must consider the general case.
; For example, if a loop uses the locals n, m, and a, you must characterize
; its behavior for arbitrary, legal n, m, and a, not just a special case (e.g.,
; where a is 0).

(defthm loop-is-helper
  (implies (and (natp x)
                (natp y))
           (equal (m1 (make-state 0
                                  (list x y)
                                  nil
                                  *pi*)
                      (loop-clk x y))
                  (make-state (if (< x y) 16 14)
                              (if (< x y)
                                  (list 0 (- y x))
                                  (list (- x y) 0))
                              (push (helper x y) nil)
                              *pi*))))

(in-theory (disable loop-clk))

(defthm program-is-fn
  (implies (ok-inputs x y)
           (equal (m1 (make-state 0
                                  (list x y)
                                  nil
                                  *pi*)
                      (clk x y))
                  (make-state (if (< x y) 16 14)
                              (if (< x y)
                                  (list 0 (- y x))
                                  (list (- x y) 0))
                              (push (fn x y) nil)
                              *pi*))))

(in-theory (disable clk))

; (7) Put the two steps together to get correctness.

(in-theory (enable fn-is-theta))

(defthm program-correct
  (implies (ok-inputs x y)
           (equal (m1 (make-state 0
                                  (list x y)
                                  nil
                                  *pi*)
                      (clk x y))
                  (make-state (if (< x y) 16 14)
                              (if (< x y)
                                  (list 0 (- y x))
                                  (list (- x y) 0))
                              (push (theta x y)
                                    nil)
                              *pi*))))

; This corollary just shows we did what we set out to do:

(defthm total-correctness
  (implies (and (natp x)
                (natp y)
                (equal sf (m1 (make-state 0
                                          (list x y)
                                          nil
                                          *pi*)
                              (clk x y))))
           (and (equal (next-inst sf) '(HALT))
                (equal (top (stack sf)) (if (< x y) 1 0))))
  :rule-classes nil)

; Think of the above theorem as saying: for all natural numbers x and y, there
; exists a clock (for example, the one constructed by (clk x y)) such that
; running *pi* with (list x y) as input produces a state, sf, that is halted
; and which contains 1 or 0 on top of the stack depending on whether x < y.
; Note that the algorithm used by *pi* is not specified or derivable from this
; formula.

