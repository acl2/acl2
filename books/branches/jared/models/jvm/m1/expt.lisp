; The Correctness of an Exponentiation Program

; Problem: Define an M1 program to compute n^m (n raised to the power m), where
; both n and m are natural numbers.

; Design Plan: I will count m down and repeatedly multiply n into an accumulator a,
; which will be initialized to 1.

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; (1) Write your specification, i.e., define the expected inputs and the
; desired output, theta.

(defun ok-inputs (n m)
  (and (natp n)
       (natp m)))

(defun theta (n m)
  (expt n m))

; (2) Write your algorithm.  This will consist of a tail-recursive helper
; function and a wrapper, fn.

(defun helper (n m a)
  (if (zp m)
      a
      (helper n (- m 1) (* n a))))

(defun fn (n m) (helper n m 1))

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.

; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n, m, and a and fn calls helper initializing a to 0, your helper theorem must
; be about (helper n m a), not just about the special case (helper n m 0).

(defthm helper-is-theta
  (implies (and (ok-inputs n m)
                (natp a))
           (equal (helper n m a)
                  (* a (theta n m)))))

(defthm fn-is-theta
  (implies (ok-inputs n m)
           (equal (fn n m)
                  (theta n m))))

; Disable these two lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper-is-theta fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.

(defconst *pi*
       '((ICONST 1)   ; 0
         (ISTORE 2)   ; 1  a = 1;
         (ILOAD 1)    ; 2  [loop:]
         (IFEQ 10)    ; 3  if m=0 then go to end;
         (ILOAD 1)    ; 4
         (ICONST 1)   ; 5
         (ISUB)       ; 6
         (ISTORE 1)   ; 7  m = m-1;
         (ILOAD 0)    ; 8
         (ILOAD 2)    ; 9
         (IMUL)       ;10
         (ISTORE 2)   ;11  a = n*a;
         (GOTO -10)   ;12  go to loop
         (ILOAD 2)    ;13  [end:]
         (HALT))      ;14 ``return'' a
    )

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun loop-clk (m)
  (if (zp m)
      3
      (clk+ 11
            (loop-clk (- m 1)))))

(defun clk (m)
  (clk+ 2
        (loop-clk m)))

; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Important Note: Your lemma about the loop must consider the general case.
; For example, if the loop uses the locals n, m, and a, you must characterize
; its behavior for arbitrary, legal n, m, and a, not just a special case (e.g.,
; where a is 0).

(defthm loop-is-helper
  (implies (and (ok-inputs n m)
                (natp a))
           (equal (m1 (make-state 2
                                  (list n m a)
                                  nil
                                  *pi*)
                      (loop-clk m))
                  (make-state 14
                              (list n 0 (helper n m a))
                              (push (helper n m a) nil)
                              *pi*))))

(in-theory (disable loop-clk))

(defthm program-is-fn
  (implies (ok-inputs n m)
           (equal (m1 (make-state 0
                                  (list n m)
                                  nil
                                  *pi*)
                      (clk m))
                  (make-state 14
                              (list n 0 (fn n m))
                              (push (fn n m) nil)
                              *pi*))))

(in-theory (disable clk))

; (7) Put the two steps together to get correctness.

(in-theory (enable fn-is-theta))

(defthm program-correct
  (implies (ok-inputs n m)
           (equal (m1 (make-state 0
                                  (list n m)
                                  nil
                                  *pi*)
                      (clk m))
                  (make-state 14
                              (list n 0 (theta n m))
                              (push (theta n m)
                                    nil)
                              *pi*))))

; This corollary just shows we did what we set out to do:

(defthm total-correctness
  (implies (and (natp n)
                (natp m)
                (equal sf (m1 (make-state 0
                                          (list n m)
                                          nil
                                          *pi*)
                              (clk m))))
           (and (equal (next-inst sf) '(HALT))
                (equal (top (stack sf)) (expt n m))))
  :rule-classes nil)

; Think of the above theorem as saying: for all natural numbers n and m, there
; exists a clock (for example, the one constructed by (clk n)) such that
; running *pi* with (list n m) as input produces a state, sf, that is halted
; and which contains (* n m) on top of the stack.  Note that the algorithm
; used by *pi* is not specified or derivable from this formula.

