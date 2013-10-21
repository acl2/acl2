; The Bogus Correctness of the Universal Function

; Problem: Define an M1 program to ``compute'' any natural number k, in the
; sense that there exists a clock that makes the program leave k on top of
; the stack (but not necessarily terminate).

; We then prove that this program is a bogusly correct way to compute the
; factorial and the Fibonacci functions.

; Design Plan: My bogusly correct universal function will just put 0 on the
; stack and then repeatedly add one to it.  So if you inspect the machine at
; just the right moment, you can see whatever natural number you want on top of
; the stack.

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; (1) Write your specification, i.e., define the expected inputs and the
; desired output, theta.

(defun ok-inputs (k)
  (natp k))

(defun theta (k)
  k)

; (2) Write your algorithm.  This will consist of a tail-recursive helper
; function and a wrapper, fn.

(defun helper (k a)
  (if (zp k)
      a
      (helper (- k 1) (+ 1 a))))

(defun fn (k) (helper k 0))

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.

; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n, m, and a and fn calls helper initializing a to 0, your helper theorem must
; be about (helper n m a), not just about the special case (helper n m 0).

(defthm helper-is-theta
  (implies (and (ok-inputs k)
                (natp a))
           (equal (helper k a)
                  (+ a (theta k)))))

(defthm fn-is-theta
  (implies (ok-inputs k)
           (equal (fn k)
                  (theta k))))

; Disable these two lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper-is-theta fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.

(defconst *pi*
       '((ICONST 0)   ; 0   tos=0;
         (ICONST 1)   ; 1 loop:
         (IADD)       ; 2   tos = tos+1;
         (GOTO -2))   ; 3   goto loop;
    )

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun loop-clk (k)
  (if (zp k)
      0
      (clk+ 3
            (loop-clk (- k 1)))))

(defun clk (k)
  (if (zp k)
      1
      (clk+ 1
            (loop-clk k))))


; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Important Note: Your lemma about the loop must consider the general case.
; For example, if the loop uses the locals n, m, and a, you must characterize
; its behavior for arbitrary, legal n, m, and a, not just a special case (e.g.,
; where a is 0).

(defthm loop-is-helper
  (implies (and (natp k)
                (natp tos))
           (equal (m1 (make-state 1
                                  locals
                                  (push tos nil)
                                  *pi*)
                      (loop-clk k))
                  (make-state 1
                              locals
                              (push (helper k tos) nil)
                              *pi*))))

(in-theory (disable loop-clk))

(defthm program-is-fn
  (implies (natp k)
           (equal (m1 (make-state 0
                                  locals
                                  nil
                                  *pi*)
                      (clk k))
                  (make-state 1
                              locals
                              (push (fn k) nil)
                              *pi*))))

(in-theory (disable clk))

; (7) Put the two steps together to get correctness.

(in-theory (enable fn-is-theta))

(defthm program-correct
  (implies (ok-inputs k)
           (equal (m1 (make-state 0
                                  locals
                                  nil
                                  *pi*)
                      (clk k))
                  (make-state 1
                              locals
                              (push (theta k)
                                    nil)
                              *pi*))))

; This corollary just shows we did what we set out to do.
; The difference between bogus-correctness and total-correctness
; is that we don't require (equal (next-inst sf) '(HALT)) below
; in the conclusion.

(defthm bogus-correctness
  (implies (and (natp k)
                (equal sf (m1 (make-state 0 locals nil *pi*)
                              (clk k))))
           (equal (top (stack sf)) k)))

; Think of the above theorem as saying: for all natural numbers k, there exists
; a clock (for example, the one constructed by (clk k)) such that running
; *pi* with any input produces a state, sf, which contains k on top of the
; stack.  Note that the algorithm used by *pi* is not specified or derivable
; from this formula.

; Consider any function that returns a natural number, e.g., fact or fib.  We
; can prove that *pi* is a ``correct'' -- in this bogus sense -- for computing
; them!

(defun fact (n)
  (if (zp n)
      1
      (* n (fact (- n 1)))))

(defun fib (n)
  (if (zp n)
      0
      (if (equal n 1)
          1
          (+ (fib (- n 1)) (fib (- n 2))))))

(defun fact-clk (n)
  (clk (fact n)))

(defun fib-clk (n)
  (clk (fib n)))

(defthm pi-bogusly-computes-fact
  (implies (and (natp n)
                (equal sf (m1 (make-state 0 (list n) nil *pi*)
                              (fact-clk n))))
           (equal (top (stack sf)) (fact n))))

; Think of the above theorem as saying: for all natural numbers n, there exists
; a clock (for example, the one constructed by (fact-clk n)) such that
; running *pi* with (list n) as input produces a state, sf, which contains
; (fact n) on top of the stack -- but isn't necessarily halted!  Note that the
; algorithm used by *pi* is not specified or derivable from this formula.


(defthm pi-bogusly-computes-fib
  (implies (and (natp n)
                (equal sf (m1 (make-state 0 (list n) nil *pi*)
                              (fib-clk n))))
           (equal (top (stack sf)) (fib n))))

; Think of the above theorem as saying: for all natural numbers n, there exists
; a clock (for example, the one constructed by (fib-clk n)) such that
; running *pi* with (list n) as input produces a state, sf, which contains (fib
; n) on top of the stack -- but isn't necessarily halted!  Note that the
; algorithm used by *pi* is not specified or derivable from this formula.



