; Correctness of Binary Exponentiation

; Problem: Define and verify an M1 program to compute (expt n m), by the binary
; method.  You may assume that n and m are natural numbers.  The ``binary
; method'' is shown by our definition of the algorithm fn below.

; Design Plan: The binary method of exponentiation involves repeated squaring.
; For example, n^11 = n*(n^10) = n*([n^2]^5).  So to compute n^m, we iterate
; counting m down by varying amounts: if m is even, we square n and divide m by
; 2.  If n is odd, we just decrement m and multiply n into our running
; accumulator a, initially 1.  Of course, to determine if m is even we'll need
; another loop.  (To compute m/2 we can just use 1/2 * m.)

; This example does three nice things:
; (a) it is the most sophisticated algorithm we'll verify here
; (b) like div.lisp, it illustrates the verification of a two-loop program
; (c) the innermost loop is coded more like a method invocation and its
;     verification foreshadows some of what we'll do when we verify
;     methods and then verify code that invokes them.

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
    (if (equal (mod m 2) 0)
        (helper (* n n) (/ m 2) a)
      (helper n (- m 1) (* n a)))))

; The problem with implementing this algorithm is that we don't have (mod m 2)
; as an M1 instruction.  We have to implement it as a separate loop to count m
; down by 2 to 0 or 1 to determine its parity.

; Also, recall in alternating-sum-variant.lisp how we had to specify the final
; value of a temporary (there it was final-sign) by writing the algorithm that
; produces it.  In this problem we have to do that, only the variable in
; question is n, which is occasionally squared in the algorithm above.  So
; here is its final value:

(defun final-n (n m)
  (if (zp m)
      n
    (if (equal (mod m 2) 0)
        (final-n (* n n) (/ m 2))
      (final-n n (- m 1)))))

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

; My program stores n and m in locals 0 and 1.  It stores a in local 2.  The
; predicate even is implemented as a loop, starting at pc = 26.  The ``invoke''
; even, I jump to that address.  Even saves the current value of local 1 by
; pushing it on the stack.  It then counts n down by 2 stopping at 0 and 1 to
; determine n's parity.  It then restores n's value from the stack, pushes a 1
; (``true'') or 0 (``false'') and ``returns'' to the caller.

(defconst *pi*
  '(
    (iconst 1)		;  0
    (istore 2)		;  1       a = 1;
                        ;    loop:
    (iload 1)		;  2
    (ifeq 21)		;  3       if m=0, goto end
    (goto 22)		;  4       ``invoke'' even
                        ;    ret-from-even:
    (ifeq 10)		;  5       if even=0, goto even-nil
    (iload 0)		;  6
    (iload 0)		;  7
    (imul)		;  8
    (istore 0)		;  9       n = n*n;
    (iload 1)		; 10
    (iconst 1/2)	; 11
    (imul)		; 12
    (istore 1)		; 13       m = m/2;
    (goto -12)		; 14       goto loop;
                        ;     even-nil:
    (iload 1)		; 15
    (iconst 1)		; 16
    (isub)		; 17
    (istore 1)		; 18       m = m-1;
    (iload 0)		; 19
    (iload 2)		; 20
    (imul)		; 21
    (istore 2)		; 22       a = n*a;
    (goto -21)		; 23       goto loop
                        ;     end:
    (iload 2)		; 24
    (halt)		; 25       return a
                        ;     even:
    (iload 1)		; 26       save m
                        ;     even-loop:
    (iload 1)		; 27
    (ifeq 10)		; 28       if m=0, goto even-t
    (iload 1)		; 29
    (iconst 1)		; 30
    (isub)		; 31
    (ifeq 9)		; 32       if m=1, goto even-nil
    (iload 1)		; 33
    (iconst 2)		; 34
    (isub)		; 35
    (istore 1)		; 36       m = m-1;
    (goto -10)		; 37       goto even-loop
                        ;    even-t:
    (istore 1)		; 38       restore m
    (iconst 1)		; 39
    (goto -35)		; 40       ``return'' 1 to ``caller''
                        ;    even-nil:
    (istore 1)		; 41       restore m
    (iconst 0)		; 42
    (goto -38)		; 43       ``return'' 0 to ``caller''
    ))

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

; (even-clk m) takes us from an ``invocation'' of even through the
; return to the caller.

(defun even-loop-clk (m) ; Assume pc = 27 = even-loop
  (if (zp m)
      5
      (if (equal m 1)
          9
          (clk+ 11
                (even-loop-clk (- m 2))))))

(defun even-clk (m) ; Assume we're at the ``invoke'' of even, pc = 4
  (clk+ 2
        (even-loop-clk m)))

; (clk m) clocks the whole computation.  It's loop-clk calls even-clk to
; when it gets to the invocation of even and assumes it leaves us at the instruction
; after the invocation.

(defun loop-clk (m)
  (if (zp m)
      3
      (if (equal (mod m 2) 0)
          (clk+ 2
                (clk+ (even-clk m)
                      (clk+ 10
                            (loop-clk (* 1/2 m)))))
          (clk+ 2
                (clk+ (even-clk m)
                      (clk+ 10
                            (loop-clk (- m 1))))))))

(defun clk (m)
  (clk+ 2
        (loop-clk m)))

; Aside: I often define a little test function to let me play with my program
; and clock.  This one prints the final pc, next-inst, locals and stack, but
; not the program.

(defun test (n m)
  (let ((sf (m1 (make-state 0 (list n m) nil *pi*)
                (clk m))))
    (list (list :pc (pc sf) '--> (next-inst sf))
          (list :locals (locals sf))
          (list :stack (stack sf)))))

; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Important Note: Your lemma about the loop must consider the general case.
; For example, if the loop uses the locals n, m, and a, you must characterize
; its behavior for arbitrary, legal n, m, and a, not just a special case (e.g.,
; where a is 0).

(defthm even-loop-is-mod=0
  (implies (natp m)
           (equal
            (m1 (make-state 27
                            (list x m y)
                            (push saved-m nil)
                            *pi*)
                (even-loop-clk m))
            (make-state 5
                        (list x saved-m y)
                        (push (if (equal (mod m 2) 0) 1 0) nil)
                        *pi*))))


(in-theory (disable even-loop-clk))

; Important Note: The following is analogous to the specification of a method
; invocation, equivalently, the addition of a new bytecode instruction.  Think
; of the ``4'' in the initial state as an arbitrary pc pointing to the
; invocation or bytecode in question.  The ``5'' in the final state is just
; pc+1.  The theorem is like the semantics of execute-EVEN: ``The pc is
; incremented by 1, the locals don't change, and a value, v, is pushed onto the
; stack, where v is 1 or 0 depending on whether local 1 is even or odd.''

(defthm even-is-mod=0
  (implies (natp m)
           (equal (m1 (make-state 4
                                  (list n m a)
                                  nil
                                  *pi*)
                      (even-clk m))
                  (make-state 5
                              (list n m a)
                              (push (if (equal (mod m 2) 0) 1 0) nil)
                              *pi*))))

(in-theory (disable even-clk))

; Once the above theorem has been proved it's as though we have a new
; instruction (except here it must be used only at pc=4!).  When symbolic
; execution gets to pc=4 with the appropriate clock, the machine just steps
; to the next instruction and pushes the value of the even predicate on stack.

(defthm helper-is-fn
  (implies (and (ok-inputs n m)
                (natp a))
           (equal (m1 (make-state 2 (list n m a) nil *pi*)
                      (loop-clk m))
                  (make-state 25
                              (list (final-n n m) 0 (helper n m a))
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
                  (make-state 25
                              (list (final-n n m) 0 (fn n m))
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
                  (make-state 25
                              (list (final-n n m) 0 (theta n m))
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
; and which contains (expt n m) on top of the stack.  Note that the algorithm
; used by *pi* is not specified or derivable from this formula.

