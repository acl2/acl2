; Correctness of Fib

; Problem: Define an M1 program to compute the Fibonacci function on its
; natural number input.  Prove your program correct.

; Fib(0) = 0
; Fib(1) = 1
; Fib(2) = Fib(1)+Fib(0)
; Fib(3) = Fib(2)+Fib(1)
; ...

; However, M1 does not have recursion or method call, so you have to do this
; iteratively.  When you verify your helper function you will have to think of
; the generalization that characterizes its output for all legal inputs, not
; just the initial case.  It also means that when you verify your loop code
; you'll have to specify the final values of ALL of the locals you're using.  I
; suggest you define the function fib-locals to return the list of the final
; values of all of the locals, rather than worry about the closed form
; expression of them.

; Design Plan: Think of the fib sequence 0, 1, 1, 2, 3, 5, 8, ... and arrange
; two auxiliary variables, j and k, to hold the first two values, 0 and 1,
; respectively.  This is a ``window'' into the sequence and it is possible to
; slide the window to the right by shifting k into j and adding k to the old
; value of j to get the new value of k.  So fib can be computed by sliding the
; window up n times.  I control the slide by counting n down to 0 by 1.  I will
; express this algorithm more precisely (and formally) when I verify it!

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; (1) Write your specification, i.e., define the expected inputs and the
; desired output, theta.

(defun ok-inputs (n)
  (natp n))

(defun fib (n)
  (if (zp n)
      0
    (if (equal n 1)
        1
      (+ (fib (- n 1))
         (fib (- n 2))))))

(defun theta (n)
  (fib n))

; (2) Write your algorithm.  This will consist of a tail-recursive helper
; function and a wrapper, fn.

(defun helper (n j k)
  (if (zp n)
      j
    (if (equal n 1)
        k
    (helper (- n 1) k (+ j k)))))

(defun fn (n) (helper n 0 1))

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.

; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n, j, and k and fn calls helper initializing j and k to 0 and 1, your helper
; theorem must be about (helper n j k), not just about the special case (helper
; n 0 1).

; It takes some creativity to figure out what the helper function does for
; arbitrary j and k (instead of the initial 0 and 1).  I figured it out by
; drawing a little table for unknown j and k but n=7:

; n            j             k
; 7            j             k  <--- unknown initial values
; 6            k           j+k
; 5          j+k          j+2k
; 4         j+2k         2j+3k
; 3        2j+3k         3j+5k
; 2        3j+5k         5j+8k
; 1        5j+8k        8j+13k

; Do you recognize the coefficients on j and k in the final line?

(defthm helper-is-theta
  (implies (and (ok-inputs n)
                (natp j)
                (natp k)
                (<= 1 n))
           (equal (helper n j k)
                  (+ (* (fib (- n 1)) j)
                     (* (fib n) k)))))

(defthm fn-is-theta
  (implies (ok-inputs n)
           (equal (fn n)
                  (theta n))))

; Disable these two lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper-is-theta fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.

(defconst *pi*
  '((iconst 0)   ;  0
    (istore 1)   ;  1  j = 0
    (iconst 1)   ;  2
    (istore 2)   ;  3  k = 1
    (iload 0)    ;  4 loop:
    (ifeq 16)    ;  5  if n=0, goto exitj
    (iload 0)    ;  6
    (iconst 1)   ;  7
    (isub)       ;  8
    (ifeq 14)    ;  9  if n=1, goto exitk
    (iload 0)    ; 10
    (iconst 1)   ; 11
    (isub)       ; 12
    (istore 0)   ; 13  n=n-1
    (iload 2)    ; 14  save k on stack
    (iload 1)    ; 15
    (iload 2)    ; 16
    (iadd)       ; 17
    (istore 2)   ; 18  k=j+k
    (istore 1)   ; 19  j= saved k
    (goto -16)   ; 20  goto loop
    (iload 1)    ; 21 exitj: return j
    (halt)       ; 22
    (iload 2)    ; 23 exitk: return k
    (halt))      ; 24
  )

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun loop-clk (n)
  (if (zp n)
      3
      (if (equal n 1)
          7
          (clk+ 17
                (loop-clk (- n 1))))))

(defun clk (n)
  (clk+ 4
        (loop-clk n)))

; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Hint: Define the function fib-locals to return the list of the final values
; of all of the locals.  We could struggle to come up with closed-form expressions
; for the final values of j and k but there's no need.  We're not interested --
; but to verify the loop we have to specify what they are, somehow.

(defun fib-locals (n j k)
  (if (zp n)
      (list n j k)
      (if (equal n 1)
          (list n j k)
          (fib-locals (- n 1) k (+ j k)))))

; Important Note: Your lemma about the loop must consider the general case.
; For example, if the loop uses the locals n, j, and k, you must characterize
; its behavior for arbitrary, legal n, j, and k, not just a special case (e.g.,
; where j and k are 0 and 1 respectively).

(defthm loop-is-helper
  (implies (and (ok-inputs n)
                (natp j)
                (natp k))
           (equal (m1 (make-state 4
                                  (list n j k)
                                  nil
                                  *pi*)
                      (loop-clk n))
                  (make-state (if (equal n 0) 22 24)
                              (fib-locals n j k)
                              (push (helper n j k) nil)
                              *pi*))))

; Contrast the statement above with what we would have to write had we NOT defined
; fib-locals:

; (defthm
;   loop-is-helper
;   (implies
;    (and (ok-inputs n) (natp j) (natp k))
;    (equal (m1 (make-state 4 (list n j k) nil *pi*)
;               (loop-clk n))
;           (make-state (if (equal n 0) 22 24)
;                       (list (if (equal n 0) 0 1)
;                             (if (equal n 0)
;                                 j
;                                 (if (equal n 1)
;                                     j
;                                     (+ (* j (fib (- n 2)))
;                                        (* k (fib (- n 1))))))
;                             (if (equal n 0)
;                                 k
;                                 (+ (* j (fib (- n 1))) (* k (fib n)))))
;                       (push (helper n j k) nil)
;                       *pi*)))
;
;   :hints (("Goal" :induct (helper n j k))))

; Of course, we first would have to figure out WHAT to write for the final values
; of j and k!  But we could, in principle, adopt this approach and modify the rest of the
; file to reflect these final values.  I won't.  Instead, I'll rely on fib-locals
; which is sort like saying ``the final locals are fib are whatever they are (as
; computed by the analogous ACL2 function.''

(in-theory (disable loop-clk))

(defthm program-is-fn
  (implies (ok-inputs n)
           (equal (m1 (make-state 0
                                  (list n)
                                  nil
                                  *pi*)
                      (clk n))
                  (make-state (if (equal n 0) 22 24)
                              (fib-locals n 0 1)
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
                  (make-state (if (equal n 0) 22 24)
                              (fib-locals n 0 1)
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
                       (fib n))))
  :rule-classes nil)

; Think of the above theorem as saying: for all natural numbers n, there exists
; a clock (for example, the one constructed by (clk n)) such that running
; *pi* with (list n) as input produces a state, sf, that is halted and which
; contains (fib n) on top of the stack.  Note that the algorithm used by *pi*
; is not specified or derivable from this formula.


