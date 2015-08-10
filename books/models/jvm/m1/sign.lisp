; Correctness of Sign

; Problem: Define an M1 program to determine the sign of an integer n.  You may
; assume that n is an integer.  To indicate that n is negative, leave -1 on the
; stack; to indicate that n is zero, leave 0 on the stack; to indicate that n
; is positive, leave +1 on the stack.  Prove that your program is correct.

; Design Plan: Since M1 can only test against 0, I have to terminate my program
; by reaching 0.  I could do that by counting a positive n down or by counting
; a negative n up.  But I don't know whether n is positive or negative.  So
; I'll start with n and -n, one of which will be positive, and count both down
; by 1.  One will reach 0 and the other will start negative and just stay
; negative.  I'll know the sign of the original n by seeing which reaches 0.

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; (1) Write your specification, i.e., define the expected inputs and the
; desired output, theta.

(defun ok-inputs (n)
  (integerp n))

(defun theta (n)
  (if (< n 0)
      -1
      (if (equal n 0)
          0
          +1)))

; (2) Write your algorithm.  This will consist of a tail-recursive helper
; function and a wrapper, fn.

(defun helper (n m)
  (declare (xargs :measure (+ (nfix m) (nfix n))))
  (if (and (integerp n)
           (integerp m)
           (or (natp n)
               (natp m)))
      (if (equal n 0)
          (if (equal m 0)
              0
              +1)
          (if (equal m 0)
              -1
              (helper (- n 1) (- m 1))))
      'illegal))

(defun fn (n) (helper n (* -1 n)))

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.


; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n and m and fn calls helper initializing m to -n, your helper theorem must
; be about (helper n m), not just about the special case (helper n (- n)).

(defthm helper-is-theta
  (implies (and (integerp n)
                (integerp m)
                (or (natp n) (natp m)))
           (equal (helper n m)
                  (if (and (natp n) (natp m))
                      (if (< n m)
                          +1
                          (if (equal n m)
                              0
                              -1))
                      (if (natp n)
                          +1
                          -1)))))

(defthm fn-is-theta
  (implies (ok-inputs n)
           (equal (fn n)
                  (theta n))))

; Disable these two lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper-is-theta fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.

(defconst *pi*
  '((ILOAD 0)   ;  0
    (ICONST -1) ;  1
    (IMUL)      ;  2
    (ISTORE 1)  ;  3 n = -m;
    (ILOAD 0)   ;  4
    (IFEQ 12)   ;  5 if m=0, goto 17
    (ILOAD 1)   ;  6
    (IFEQ 16)   ;  7 if n=0, goto 23
    (ILOAD 0)   ;  8
    (ICONST 1)  ;  9
    (ISUB)      ; 10
    (ISTORE 0)  ; 11 m = m-1;
    (ILOAD 1)   ; 12
    (ICONST 1)  ; 13
    (ISUB)      ; 14
    (ISTORE 1)  ; 15 n = n-1;
    (GOTO -12)  ; 16 goto 4
    (ILOAD 1)   ; 17
    (IFEQ 3)    ; 18 if n=0, goto 21
    (ICONST 1)  ; 19 answer: positive
    (GOTO 4)    ; 20 goto 24
    (ICONST 0)  ; 21 answer: zero
    (GOTO 2)    ; 22 goto 24
    (ICONST -1) ; 23 answer: negative
    (HALT))     ; 24 halt
  )

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun loop-clk (n m)
  (declare (xargs :measure (+ (nfix n) (nfix m))))
  (cond ((and (integerp n)
              (integerp m)
              (or (natp n)
                  (natp m)))
         (cond ((equal n 0)
                6)
               ((equal m 0)
                5)
               (t (clk+ 13
                        (loop-clk (- n 1) (- m 1))))))
        (t nil)))

(defun clk (n)
  (clk+ 4
        (loop-clk n (- n))))

; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Important Note: Your lemma about the loop must consider the general case.
; For example, if the loop uses the locals n and m, you must characterize its
; behavior for arbitrary, legal n and m, not just a special case (e.g., where n
; is (- n)).

(defthm loop-is-helper
  (implies (and (integerp n)
                (integerp m)
                (or (natp n) (natp m)))
           (equal (m1 (make-state 4
                                  (list n m)
                                  nil
                                  *pi*)
                      (loop-clk n m))
                  (make-state 24
                              (cond
                               ((and (natp n) (natp m))
                                (if (< n m)
                                    (list 0 (- m n))
                                    (list (- n m) 0)))
                               ((natp n)
                                (list 0 (- m n)))
                               (t (list (- n m) 0)))
                              (push (helper n m) nil)
                              *pi*))))

(in-theory (disable loop-clk))

(defthm program-is-fn
  (implies (ok-inputs n)
           (equal (m1 (make-state 0
                                  (list n)
                                  nil
                                  *pi*)
                      (clk n))
                  (make-state 24
                              (if (natp n)
                                  (list 0 (* -2 n))
                                  (list (* 2 n) 0))
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
                  (make-state 24
                              (if (natp n)
                                  (list 0 (* -2 n))
                                  (list (* 2 n) 0))
                              (push (theta n)
                                    nil)
                              *pi*))))

; This corollary just shows we did what we set out to do:

(defthm total-correctness
  (implies (and (integerp n)
                (equal sf (m1 (make-state 0
                                          (list n)
                                          nil
                                          *pi*)
                              (clk n))))
           (and (equal (next-inst sf) '(HALT))
                (equal (top (stack sf))
                       (if (< n 0)
                           -1
                           (if (equal n 0)
                               0
                               +1)))))
  :rule-classes nil)

; Think of the above theorem as saying: for all integers n, there exists a
; clock (for example, the one constructed by (clk n)) such that running
; *pi* with (list n) as input produces a state, sf, that is halted and which
; contains -1, 0, or +1 on top of the stack depending on whether x is negative,
; 0, or positive.  Note that the algorithm used by *pi* is not specified or
; derivable from this formula.

