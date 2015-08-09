; Correctness of Division

; Problem: Define an M1 program to compute the natural number quotient (i.e.,
; the floor) of n divided by d, where n and d are natural numbers and d is not
; 0.  Prove that your program is correct.  Note: In ACL2, the floor of n
; divided by d is (floor n d), e.g., (floor 27 6) = 4.

; Design Plan: I will count how many times I can take d away from n before n <
; d.  I will keep the counter in an auxilliary variable, a.  However, I can't
; test n < d directly with M1, so I have to implement that test with a loop.
; So my solution will be a program with nested loops.  To test n < d I'll move
; both n and d into two additional auxiliary variables, x and y, so I can count
; them down without destroying n and d.

; Because of the nested loops, this file deviates a little from our one-loop
; template, but I'll preserve the template's names for the main algorithm and
; its outer loop.

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; (1) Write your specification, i.e., define the expected inputs and the
; desired output, theta.

(defun ok-inputs (n d)
  (and (natp n)
       (natp d)
       (not (equal d 0))))

(defun theta (n d)
  (floor n d))

; (2) Write your algorithm.  This will consist of a tail-recursive helper
; function and a wrapper, fn.

; Recall the lessp problem (see lessp.lisp).  We need that concept here.  It
; will be the ``helper's helper'' but we call it ``lessp'' instead.  Every part
; of this problem concerned with lessp is analogous to what we did in
; lessp.lisp, but because we don't have method invocation we have to
; ``re-verify'' the code.

(defun lessp (x y)
  (cond ((zp y) 0)
        ((zp x) 1)
        (t (lessp (- x 1) (- y 1)))))

; Here is the lemma that says the helper's helper does what we intended.

(defthm lessp-lemma
  (implies (and (natp x)
                (natp y))
           (equal (lessp x y)
                  (if (< x y) 1 0))))

; By the way, the theorem above ``ought'' to have been proved below when we
; prove the relations between the algorithms and the spec.  But we actually
; need to know (lessp x y) ``is'' (< x y) to know that the helper terminates.
; That's why we proved it ``early.''  It is not unusual in real projects to see
; the template ``mixed up'' like this.

; When you read the next defun, ignore rest for a moment!

(defun helper (n d a rest)
  (declare (ignore rest))
  (if (and (natp n)
           (natp d)
           (not (equal d 0)))
      (if (equal (lessp n d) 1)
          a
          (helper (- n d) d (+ 1 a) (list (- n d) 0)))
      'illegal))

; The role of rest in the definition of helper is very subtle.  Note that rest
; is an argument that we explicitly ignore and but go to the bother of
; specifying what its value is on each recursive call of helper.  We'll explain
; the role of rest in helper later.  For now, just keep reading, recognizing
; that we're following the template.

(defun fn (n d)
  (helper n d 0 nil))

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.

; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n, m, a, and rest and fn calls helper initializing a to 0 and rest to nil,
; your helper theorem must be about (helper n m a rest), not just about the
; special case (helper n m 0 nil).

(defthm helper-is-theta
  (implies (and (natp n)
                (natp d)
                (not (equal d 0))
                (natp a))
           (equal (helper n d a rest)
                  (+ a (theta n d)))))

(defthm fn-is-theta
  (implies (ok-inputs n m)
           (equal (fn n m)
                  (theta n m))))

; Disable these two lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper-is-theta fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.

(defconst *pi*

; We compute (div n d), where n and d are naturals and d is not
; zero.  We use the following locals:
; 0 n
; 1 d
; 2 a - answer
; 3 x - param for lessp
; 4 y - param for lessp
  '((iconst 0)  ;  0
    (istore 2)  ;  1   a = 0
    (iload 0)   ;  2   loop:
    (istore 3)  ;  3   x = n
    (iload 1)   ;  4
    (istore 4)  ;  5   y = d
; (invoke lessp on n d)....
    (iload 4)   ;  6   lessp-loop:          -- the code for lessp
    (ifeq 12)   ;  7   if y=0, goto false
    (iload 3)   ;  8
    (ifeq 12)   ;  9   if x=0, goto to true
    (iload 3)   ; 10
    (iconst 1)  ; 11
    (isub)      ; 12
    (istore 3)  ; 13   x = x-1
    (iload 4)   ; 14
    (iconst 1)  ; 15
    (isub)      ; 16
    (istore 4)  ; 17   y = y-1
    (goto -12)  ; 18   goto lessp-loop
    (iconst 0)  ; 19   lessp is false
    (goto 2)    ; 20
    (iconst 1)  ; 21   lessp is true
    (ifeq 3)    ; 22   if (n >= d) goto continue
    (iload 2)   ; 23
    (halt)      ; 24   return a
    (iload 0)   ; 25   continue:
    (iload 1)   ; 26
    (isub)      ; 27
    (istore 0)  ; 28   n = n-d
    (iload 2)   ; 29
    (iconst 1)  ; 30
    (iadd)      ; 31
    (istore 2)  ; 32   a = a+1
    (goto -31)  ; 33   goto loop
    ))

; Note: We can now foreshadow a little the role of rest in helper.  The outer
; loop, which helper models, starts at pc=2.  Upon the first arrival at pc=2,
; there are exactly 3 locals, n, d, and a.  But upon the next and all
; subsequent arrivals there are 5 locals: x and y were added when we invoked
; the inner loop.  The first three arguments of helper are the contents of the
; first three locals at the top of the outer loop.  The rest argument of helper
; is a list containing the rest of the locals.  Keep reading the template and
; we'll explain the role of rest in helper soon.

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun inner-loop-clk (x y)
  (if (zp y)
      4
      (if (zp x)
          5
          (clk+ 13
                (inner-loop-clk (- x 1) (- y 1))))))

(defun outer-loop-clk (n d)
  (if (and (natp n)
           (natp d)
           (not (equal d 0)))
      (if (< n d)
          (clk+ 4
                (clk+ (inner-loop-clk n d)
                      2))
          (clk+ 4
                (clk+ (inner-loop-clk n d)
                      (clk+ 10
                            (outer-loop-clk (- n d) d)))))
      nil))

(defun clk (n d)
  (clk+ 2
        (outer-loop-clk n d)))

; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Important Note: Your lemmas about your loops must consider the general case.
; For example, if a loop uses the locals n, m, and a, you must characterize
; its behavior for arbitrary, legal n, m, and a, not just a special case (e.g.,
; where a is 0).

(defthm inner-loop-is-lessp
  (implies (and (natp x)
                (natp y))
           (equal (m1 (make-state 6
                                  (list n d a x y)
                                  nil
                                  *pi*)
                      (inner-loop-clk x y))
                  (make-state 22
                              (if (< x y)
                                  (list n d a 0 (- y x))
                                  (list n d a (- x y) 0))
                              (push (lessp x y) nil)
                              *pi*))))

(in-theory (disable inner-loop-clk))

; Note: Now we explain the role of rest in helper.  Note the locals of the
; initial state.  (List* n d a rest) is a list whose first three elements are
; n, d, and a, and whose remaining elements are those of rest.  The hypothesis
; stipulates that upon the arrivial at the top of the outer loop (pc = 2) rest
; is either nil or list containing exactly two more locals.

; Of course, this theorem is proved by induction.  The induction hypothesis is
; formed by replacing the variables below, n d, a, and rest, by new values as
; done by some recursive function in the formula.  Helper is actually telling
; the theorem prover what values to use for those variables -- including the
; value of rest when we've traversed the loop.

(defthm outer-loop-is-helper
  (implies (and (natp n)
                (natp d)
                (not (equal d 0))
                (natp a)
                (or (equal rest nil)
                    (equal (cdr (cdr rest)) nil)))
           (equal (m1 (make-state 2
                                  (list* n d a rest)
                                  nil
                                  *pi*)
                      (outer-loop-clk n d))
                  (make-state 24
                              (list (mod n d)
                                    d
                                    (helper n d a rest)
                                    0
                                    (- d (mod n d)))
                              (push (helper n d a rest) nil)
                              *pi*))))

(in-theory (disable outer-loop-clk))

(defthm program-is-fn
  (implies (ok-inputs n d)
           (equal (m1 (make-state 0
                                  (list n d)
                                  nil
                                  *pi*)
                      (clk n d))
                  (make-state 24
                              (list (mod n d) d (fn n d) 0 (- d (mod n d)))
                              (push (fn n d) nil)
                              *pi*))))

(in-theory (disable clk))

; (7) Put the two steps together to get correctness.

(in-theory (enable fn-is-theta))

(defthm program-correct
  (implies (ok-inputs n d)
           (equal (m1 (make-state 0
                                  (list n d)
                                  nil
                                  *pi*)
                      (clk n d))
                  (make-state 24
                              (list (mod n d) d (theta n d) 0 (- d (mod n d)))
                              (push (theta n d)
                                    nil)
                              *pi*))))

; This corollary just shows we did what we set out to do:

(defthm total-correctness
  (implies (and (natp n)
                (natp d)
                (not (equal d 0))
                (equal sf (m1 (make-state 0
                                          (list n d)
                                          nil
                                          *pi*)
                              (clk n d))))
           (and (equal (next-inst sf) '(HALT))
                (equal (top (stack sf)) (floor n d))))
  :rule-classes nil)

; Think of the above theorem as saying: for all natural numbers n and d, there
; exists a clock (for example, the one constructed by (clk n d)) such that
; running *pi* with (list n d) as input produces a state, sf, that is halted
; and which contains (floor n d) on top of the stack.  Note that the algorithm
; used by *pi* is not specified or derivable from this formula.

