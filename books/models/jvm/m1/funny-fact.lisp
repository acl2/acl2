; Correctness of a Factorial Program that Violates Actual JVM Stack Rules

; Problem: Define an M1 program to compute the factorial of a natural number n,
; by pushing all the factors onto the stack and then multiplying them in a second
; loop.

; Design Plan: I will go around a loop pushing n, n-1, ..., 1 onto the stack.
; Then I will go around another loop just doing IMULs.  Note that I must go
; around the first loop n times and the second loop n-1 times.  This program
; violates the bytecode verifier's run that the stack is a fixed size at every
; instruction.

; Verification of the program illustrates how to verify a two loop program
; where the loops are not nested.  However, this program is very unusual
; because it essentially uses the stack as a list of values of arbitary length
; and its verification involves abandoning the push/top/pop abstraction and
; just manipulating lists.  (Of course, we could redevelop list theory for
; push/top/pop, but it is counter to the spirit of stacks.)  So this is not a
; good exemplar of two-loop verification.

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; (1) Write your specification, i.e., define the expected inputs and the
; desired output, theta.

(defun ok-inputs (n)
  (natp n))

(defun ! (n)
  (if (zp n)
      1
      (* n (! (- n 1)))))

(defun theta (n)
  (! n))

; (2) Write your algorithm.  This will consist of a tail-recursive helper
; function and a wrapper, fn.

; With this algorithm we see something new: We have to have two loops and so we
; have to have two helpers, one which is mimicking pushing things onto the
; stack and the other which mimicks IMULing them away.  Unlike our other
; helpers, these return the stack rather than some individual local.

(defun helper1 (n stack)
  (if (zp n)
      stack
      (helper1 (- n 1) (push n stack))))

(defun helper2 (m stack)
  (if (zp m)
      stack
      (helper2 (- m 1) (push (* (top (pop stack)) (top stack)) (pop (pop stack))))))

(defun fn (n)
  (if (zp n)
      1
      (top (helper2 (- n 1)
                    (helper1 n nil)))))

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.

; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n, m, and a and fn calls helper initializing a to 0, your helper theorem must
; be about (helper n m a), not just about the special case (helper n m 0).

; -----------------------------------------------------------------

; Here begins a horrible development of list theory and the conversion of our
; stack stuff to lists!  We could import a bunch of functions from ACL2 list
; books, but I'll just develop it all here.  The end of this development is
; marked by another row of hyphens.

(in-theory (enable top pop push))

(defun ap (x y)
  (if (endp x)
      y
      (cons (car x)
            (ap (cdr x) y))))

(defun nats (n)
  (if (zp n)
      nil
      (ap (nats (- n 1)) (list n))))

(defun prod (x)
  (if (endp x)
      1
      (* (car x) (prod (cdr x)))))

(defun firstn (n x)
  (if (or (zp n)
          (endp x))
      1
      (cons (car x)
            (firstn (- n 1) (cdr x)))))

(defun natp-list (x)
  (if (endp x)
      t
      (and (natp (car x))
           (natp-list (cdr x)))))

(defthm assoc-of-ap
  (equal (ap (ap a b) c)
         (ap a (ap b c))))

(defthm natp-list-ap
  (equal (natp-list (ap a b))
         (and (natp-list a)
              (natp-list b))))

(defthm len-ap
  (equal (len (ap a b))
         (+ (len a) (len b))))

(defthm len-nats
  (equal (len (nats n))
         (nfix n)))

(defthm natp-list-nats
  (natp-list (nats n)))

(defthm firstn-ap
  (implies (natp n)
           (equal (firstn n (ap a b))
                  (if (< n (len a))
                      (firstn n a)
                      (ap a (firstn (- n (len a)) b))))))

(defthm prod-ap
  (equal (prod (ap a b))
         (* (prod a) (prod b))))

(defthm prod-nats
  (equal (prod (nats n))
         (! (nfix n))))

(defthm nthcdr-ap
  (implies (natp n)
           (equal (nthcdr n (ap a b))
                  (if (< n (len a))
                      (ap (nthcdr n a) b)
                      (nthcdr (- n (len a)) b)))))

; -----------------------------------------------------------------

(defthm helper1-alt-def
  (equal (helper1 n stack)
         (ap (nats n) stack)))

(defthm helper2-alt-def
  (implies (and (natp n)
                (natp-list stack)
                (< n (len stack)))
           (equal (helper2 n stack)
                  (cons (prod (firstn (+ n 1) stack))
                        (nthcdr (+ n 1) stack)))))

(defthm helper2-helper1-is-theta
  (implies (and (not (zp n))
                (natp-list stack))
           (equal (helper2 (- n 1) (helper1 n stack))
                  (push (! n) stack))))

(defthm fn-is-theta
  (implies (ok-inputs n)
           (equal (fn n) (theta n))))

; Disable these lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper1-alt-def
                    helper2-alt-def
                    helper2-helper1-is-theta
                    fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.

(defconst *pi*
       '((ILOAD 0)   ;  0
         (IFEQ 21)   ;  1
         (ILOAD 0)   ;  2
         (ICONST 1)  ;  3
         (ISUB)      ;  4
         (ISTORE 1)  ;  5
         (ILOAD 0)   ;  6 loop1
         (IFEQ 7)    ;  7
         (ILOAD 0)   ;  8
         (ILOAD 0)   ;  9
         (ICONST 1)  ; 10
         (ISUB)      ; 11
         (ISTORE 0)  ; 12
         (GOTO -7)   ; 13
         (ILOAD 1)   ; 14 loop2
         (IFEQ 8)    ; 15
         (IMUL)      ; 16
         (ILOAD 1)   ; 17
         (ICONST 1)  ; 18
         (ISUB)      ; 19
         (ISTORE 1)  ; 20
         (GOTO -7)   ; 21
         (ICONST 1)  ; 22
         (HALT))     ; 23
    )

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun loop1-clk (n)
  (if (zp n)
      2
      (clk+ 8
            (loop1-clk (- n 1)))))

(defun loop2-clk (m)
  (if (zp m)
      2
      (clk+ 8
            (loop2-clk (- m 1)))))

(defun clk (n)
  (if (zp n)
      8
      (clk+ 6
            (clk+ (loop1-clk n)
                  (loop2-clk (- n 1))))))


; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Important Note: Your lemma about the loop must consider the general case.
; For example, if the loop uses the locals n, m, and a, you must characterize
; its behavior for arbitrary, legal n, m, and a, not just a special case (e.g.,
; where a is 0).

(defthm loop1-is-helper1
  (implies (ok-inputs n)
           (equal (m1 (make-state 6
                                  (list n m)
                                  stack
                                  *pi*)
                      (loop1-clk n))
                  (make-state 14
                              (list 0 m)
                              (helper1 n stack)
                              *pi*))))

(in-theory (disable loop1-clk))

(defthm loop2-is-helper2
  (implies (and (natp m)
                (natp-list stack)
                (< m (len stack)))
           (equal (m1 (make-state 14
                                  (list n m)
                                  stack
                                  *pi*)
                      (loop2-clk m))
                  (make-state 23
                              (list n 0)
                              (helper2 m stack)
                              *pi*))))

(in-theory (disable loop2-clk))

(defthm program-is-fn
  (implies (ok-inputs n)
           (equal (m1 (make-state 0
                                  (list n)
                                  nil
                                  *pi*)
                      (clk n))
                  (make-state 23
                              (if (zp n) (list 0) (list 0 0))
                              (push (fn n) nil)
                              *pi*)))
; This hint is necessary because we have to relieve the hypotheses on the two
; loop lemmas, e.g., that stack is a list of nats sufficiently long, and our
; way of doing that is to appeal to the list lemmas.

  :hints (("Goal" :in-theory (enable helper1-alt-def helper2-alt-def))))

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
                  (make-state 23
                              (if (zp n) (list 0) (list 0 0))
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
                (equal (top (stack sf)) (! n))))
  :rule-classes nil)

; Think of the above theorem as saying: for all natural numbers n and m, there
; exists a clock (for example, the one constructed by (clk n)) such that
; running *pi* with (list n m) as input produces a state, sf, that is halted
; and which contains (* n m) on top of the stack.  Note that the algorithm
; used by *pi* is not specified or derivable from this formula.

