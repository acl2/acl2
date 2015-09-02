; Correctness of Even

; Problem: Define an M1 program that determines if its argument, n, is even or
; odd.  You may assume n is a natural number.  To indicate that n is even,
; leave 1 on the stack.  Otherwise, leave 0 on the stack.  Prove that your
; program is correct.

; Advice: A convenient expression of the idea ``n is even'' in ACL2 is the
; expression (equal (mod n 2) 0).  That is, provided n is a natural number,
; (equal (mod n 2) 0) is t if n is even and is nil if n is odd.

; Design Plan: I will count n down to 0 by 1 and flip a bit each time.  The bit
; will start at 1.  If n is even, the final bit will be 1 (``true'') because
; I'll have flipped it an even number of times; else it will be 0 (``false'')
; because I'll have flipped it an odd number of times.

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; (1) Write your specification, i.e., define the expected inputs and the
; desired output, theta.

(defun ok-inputs (n)
  (natp n))

(defun theta (n)
  (if (equal (mod n 2) 0) 1 0))

; (2) Write your algorithm.  This will consist of a tail-recursive helper
; function and a wrapper, fn.

(defun helper (n bit)
  (if (zp n)
      bit
      (helper (- n 1) (if (equal bit 0) 1 0))))

(defun fn (n) (helper n 1))

; Note: Since the wrapper fn is just the helper, we don't need both.  But we'll
; stick to the template.

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.

; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n, m, and a and fn calls helper initializing a to 0, your helper theorem must
; be about (helper n m a), not just about the special case (helper n m 0).

(defthm helper-is-theta
  (implies (and (ok-inputs n)
                (or (equal bit 0)
                    (equal bit 1)))
           (equal (helper n bit)
                  (if (equal (theta n) 0) ; n is odd
                      (if (equal bit 0) 1 0)
                      bit))))


(defthm fn-is-theta
  (implies (ok-inputs n)
           (equal (fn n)
                  (theta n))))

; Disable these two lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper-is-theta fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.

(defconst *pi*
  '((ICONST 1)
    (ISTORE 1)
    (ILOAD 0)   ; loop = pc 2
    (IFEQ 12)
    (ILOAD 0)
    (ICONST 1)
    (ISUB)
    (ISTORE 0)
    (ILOAD 1)   ; the next 6 instrs flip bit.  That could be done with
    (IFEQ 3)    ; (ILOAD 0) (ICONST -1)(IMUL)(ICONST 1)(IADD)(ISTORE 0)
    (ICONST 0)  ; but that sequence takes 6 TICKs and this one takes
    (GOTO 2)    ; either 4 or 5 depending on bit.
    (ICONST 1)
    (ISTORE 1)
    (GOTO -12)
    (ILOAD 1)
    (HALT))
  )

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun loop-clk (n bit)
  (if (zp n)
      3
      (if (equal bit 0)
          (clk+ 11
                (loop-clk (- n 1) 1))
          (clk+ 12
                (loop-clk (- n 1) 0)))))

(defun clk (n)
  (clk+ 2
        (loop-clk n 1)))

(defun test (n)
  (let ((sf (m1 (make-state 0 (list n) nil *pi*) (clk n))))
    (list (list :pc (pc sf) '--> (next-inst sf))
          (list :locals (locals sf))
          (list :stack (stack sf)))))

; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Note: The lemma below is a bit tricky because we have to specify the values
; left in the locals at the end of the run.  What is left in local 0, i.e.,
; what is the final value of n?  It is either 0 or 1, i.e., it is (mod n 2).
; This is the first time we have had to introduce a ``new'' function to specify
; a loop's behavior.  But it happens often.

; Important Note: Your lemma about the loop must consider the general case.
; For example, if the loop uses the locals n, m, and a, you must characterize
; its behavior for arbitrary, legal n, m, and a, not just a special case (e.g.,
; where a is 0).

(defthm loop-is-helper
  (implies (and (ok-inputs n)
                (or (equal bit 0)
                    (equal bit 1)))
           (equal (m1 (make-state 2
                                  (list n bit)
                                  nil
                                  *pi*)
                      (loop-clk n bit))
                  (make-state 16
                              (list 0 (helper n bit))
                              (push (helper n bit) nil)
                              *pi*))))

(in-theory (disable loop-clk))

(defthm program-is-fn
  (implies (ok-inputs n)
           (equal (m1 (make-state 0
                                  (list n)
                                  nil
                                  *pi*)
                      (clk n))
                  (make-state 16
                              (list 0 (fn n))
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
                  (make-state 16
                              (list 0 (theta n))
                              (push (theta n)
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
                       (if (equal (mod n 2) 0)
                           1
                           0))))
  :rule-classes nil)

; Think of the above theorem as saying: for all natural numbers n, there exists
; a clock (for example, the one constructed by (clk n)) such that running
; *pi* with (list n) as input produces a state, sf, that is halted and which
; contains 1 or 0 on top of the stack depending on whether n is even.  Note
; that the algorithm used by *pi* is not specified or derivable from this
; formula.

