; Correctness of Sum

; Problem: Define an M1 program to compute the ceiling of n divided by 2 via
; the ``alternating sum'' the natural number n.  The alternating sum of 7 is
; 7-6+5-4+3-2+1-0 = 4 = (acl2::ceiling n 2).  Prove your program correct.

; Design Plan: I will have two auxiliary variables, a sign and an accumulator
; a.  The sign will be either -1 or +1, indicating the sign of the next term.
; It will start at +1 and a will start at 0.  I will count n down to 0 by 1
; adding either each successive result or its negation into a, according to
; sign.  I'll flip sign on each iteration.

; We presented one solution to this in alternating-sum.lisp.  This solution is
; exactly the same as far as the algorithm and code are concerned.  But my
; approach to the proof is a little different.  In the previous solution we had
; to specify the final value of the variable SIGN in our specification and
; program.  We found a closed-form expression for it, namely (if (equal (mod n
; 2) 0) sign (- sign)).  But sometimes it is hard to find a closed-form
; expression for a quantity you're not very interested in.  So we show another
; way to handle it here: define an ACL2 function that computes it the same way
; the algorithm does.

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; (1) Write your specification, i.e., define the expected inputs and the
; desired output, theta.

(defun ok-inputs (n)
  (natp n))

(defun theta (n)
  (ceiling n 2))

; (2) Write your algorithm.  This will consist of a tail-recursive helper
; function and a wrapper, fn.

(defun helper (n sign a)
  (if (zp n)
      a
      (helper (- n 1)
              (* -1 sign)
              (+ a (* sign n)))))

(defun fn (n) (helper n +1 0))

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.

; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n and a and fn calls helper initializing a to 0, your helper theorem must
; be about (helper n a), not just about the special case (helper n 0).

(defthm helper-is-theta
  (implies (and (ok-inputs n)
                (or (equal sign +1)
                    (equal sign -1))
                (integerp a))
           (equal (helper n sign a)
                  (+ a (* sign (theta n))))))

(defthm fn-is-theta
  (implies (ok-inputs n)
           (equal (fn n)
                  (theta n))))

; Disable these two lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper-is-theta fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.

(defconst *pi*
  '((iconst +1)  ;  0
    (istore 1)   ;  1
    (iconst 0)   ;  2
    (istore 2)   ;  3
    (iload 0)    ;  4
    (ifeq 16)    ;  5
    (iload 2)    ;  6
    (iload 1)    ;  7
    (iload 0)    ;  8
    (imul)       ;  9
    (iadd)       ; 10
    (istore 2)   ; 11
    (iload 1)    ; 12
    (iconst -1)  ; 13
    (imul)       ; 14
    (istore 1)   ; 15
    (iload 0)    ; 16
    (iconst 1)   ; 17
    (isub)       ; 18
    (istore 0)   ; 19
    (goto -16)   ; 20
    (iload 2)    ; 21
    (halt))      ; 22
  )

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun loop-clk (n)
  (if (zp n)
      3
      (clk+ 17
            (loop-clk (- n 1)))))

(defun clk (n)
  (clk+ 4
        (loop-clk n)))

; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Important Note: Your lemma about the loop must consider the general case.
; For example, if the loop uses the locals n and a, you must characterize
; its behavior for arbitrary, legal n and a, not just a special case (e.g.,
; where a is 0).

; Idea of this Variant: In the solution of this problem titled
; alternating-sum.lisp, we showed that the final value of the sign (i.e., of
; local 1) is (if (equal (mod n 2) 0) sign (- sign)).  Instead of having to
; discover this closed form expression of it, we could just define the function
; that computes it the same way the program does.  In this approach, we might
; have named helper ``final-a''.

(defun final-sign (n sign)
  (if (zp n)
      sign
      (final-sign (- n 1) (- sign))))

(defthm loop-is-helper
  (implies (and (ok-inputs n)
                (or (equal sign +1)
                    (equal sign -1))
                (integerp a))
           (equal (m1 (make-state 4
                                  (list n sign a)
                                  nil
                                  *pi*)
                      (loop-clk n))
                  (make-state 22
                              (list 0 (final-sign n sign) (helper n sign a))
                              (push (helper n sign a) nil)
                              *pi*))))

(in-theory (disable loop-clk))

(defthm program-is-fn
  (implies (ok-inputs n)
           (equal (m1 (make-state 0
                                  (list n)
                                  nil
                                  *pi*)
                      (clk n))
                  (make-state 22
                              (list 0 (final-sign n 1) (fn n))
                              (push (fn n) nil)
                              *pi*))))

(in-theory (disable clk))

; (7) Put the two steps together to get correctness.

(in-theory (enable fn-is-theta))

(defthm program-correct
  (implies (ok-inputs n)
           (equal (m1 (make-state 0
                                  (list n)
                                  nil
                                  *pi*)
                      (clk n))
                  (make-state 22
                              (list 0 (final-sign n 1) (ceiling n 2))
                              (push (ceiling n 2)
                                    nil)
                              *pi*))))

; This corollary just shows we did what we set out to do:

(defthm total-correctness
  (implies (and (natp n)
                (equal sf (m1 (make-state 0
                                          (list n)
                                          nil
                                          *pi*)
                              (clk n))))
           (and (equal (next-inst sf) '(HALT))
                (equal (top (stack sf))
                       (ceiling n 2))))
  :rule-classes nil)

; Think of the above theorem as saying: for all natural numbers n, there exists
; a clock (for example, the one constructed by (clk n)) such that running
; *pi* with (list n) as input produces a state, sf, that is halted and which
; contains (ceiling n 2) on top of the stack.  Note that the algorithm used by
; *pi* is not specified or derivable from this formula.

