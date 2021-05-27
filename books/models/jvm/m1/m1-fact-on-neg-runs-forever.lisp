; Certification Instructions:
; (include-book "models/jvm/m1/m1" :dir :system)
; (include-book "misc/defpun" :dir :system)
; (certify-book "/u/moore/text/acl2-intro/plenary-j1/m1-fact-on-neg-runs-forever" 2)

; The M1 Factorial Program Runs Forever if Input n is Negative
; J Moore

; We often prove theorems about programs being run by a formal operational
; semantics that is given by an iterated STEP function, e.g., (M1 st k) where
; st is a ``state'' object and k is some number of steps to take.  A typical
; ``total correctness'' theorem is logically something like this: if the
; initial state is ok (i.e., the desired program is in the program
; component/memory region of the state s0, the pc points to the top of the
; program, and the stack and registers are initialized in accordance with the
; program's ``pre-conditions'') then THERE EXISTS a k such that (m1 s0 k) is
; halted and the right answer is found at the expected place (e.g., the top of
; the stack).  But ACL2 doesn't have an existential quantifier.  So we
; typically define a ``clock function'' that counts the number of steps from
; program entry to the HALT, as a function of the inputs.  There are many
; examples this approach in books/models/jvm/m1/*.lisp.  A total correctness
; theorem and proof for the factorial when it is given a natural number input,
; below, may be found on that directory in fact.lisp.  (We can, of course, use
; other methods, e.g., inductive assertions proved directly from the M1
; semantics.)

; However, we are often asked ``Can you use clock functions to prove anything
; about programs that don't terminate?''  The answer is yes and this file
; demonstrates a technique.

; We prove that the fact program (whose total correctness on natural numbers is
; referenced above) does not terminate on negative integers.

; We prove this two ways.  First, we use the standard clock approach to show
; that we never get out of the loop.  Second, we use inductive assertions to
; prove that we never reach pc 14 where the only (HALT) is.

(in-package "M1")

(defconst *fact* ; M1 program to compute factorial

; Register numbers: 0, 1
; My names:         n, a

       '((ICONST 1)  ; 0
         (ISTORE 1)  ; 1     a := 1
         (ILOAD 0)   ; 2  loop: (pc = 2)
         (IFEQ 10)   ; 3     if n=0 goto end (pc = 3+10)
         (ILOAD 0)   ; 4
         (ILOAD 1)   ; 5
         (IMUL)      ; 6
         (ISTORE 1)  ; 7     a := n*a
         (ILOAD 0)   ; 8
         (ICONST -1) ; 9
         (IADD)      ;10
         (ISTORE 0)  ;11     n := n-1
         (GOTO -10)  ;12     goto loop (pc = 12-10)
         (ILOAD 1)   ;13  end: (pc = 13)
         (HALT))     ;14     ``return'' a (on top of stack)
       )

; We first define the clock function that drives the program from the loop that
; starts at pc=2 until it arrives back at the loop with less than 12 ticks left
; on the clock.

(defun fact-of-neg-at-loop-clk (k n a)
  (declare (ignorable n a))
  (if (natp k)
      (if (< k 12)
          k
          (clk+ 11 (fact-of-neg-at-loop-clk (- k 11) (- n 1) (* n a))))
      k))

; Then we define the clock that takes 0 or 1 steps and otherwise uses the clock
; above because if we take 2 steps we've arrived at the loop at pc = 2.

(defun fact-of-neg-clk (k n)
  (if (natp k)
      (if (equal k 0)
          0
          (if (equal k 1)
              1
              (clk+ 2 (fact-of-neg-at-loop-clk (- k 2) n 1))))
      k))

; A fact about (fact-of-neg-clk k n) is that it is equal to k.  But we don't
; reveal that fact to ACL2 yet.

; These clock functions are VERY SPECIAL.  First, they destructure any k into
; 2+11+11...+(mod k-2 11).  The series 11+11+... will repeatedly drive the
; program around the loop if we start at pc=2.  Furthermore, the values given
; in the recursive calls specify the values of N and A at each step.  This sets
; up a perfect inductive proof if we induct on k this way.

; This function computes the value of variable A (register 1) upon the last
; arrival at the loop.

(defun a-value (i n a)
  (if (zp i)
      a
      (a-value (- i 1) (- n 1) (* n a))))

; This lemma is a dangerous one that simplifies any term of the form (< x k) to
; x=0, x=1, ..., x=k-1, provided x is an integer and k is a positive natural
; constant, e.g., (quote 12).  Normally one would not want to do this case
; split.  But our reasoning is as follows.  Once we get to the last arrival at
; the loop there are less than 12 ticks left on the clock and just prove
; whatever we're proving by running the program on each of the possibilities.

(defthm case-splitter
  (implies (and (integerp x)
                (natp k)
                (not (equal k 0))
                (syntaxp (and (quotep k)
                              (natp (cadr k)))))
           (equal (< x k)
                  (or (equal x (- k 1))
                      (< x (- k 1))))))

; This is the key lemma.  It says that if the state is at the top of the loop
; and n is negative, then running (fact-of-neg-at-loop-clk k n a) steps leaves
; you at the top of the loop with n even more negative and a certain
; (irrelevant) value in a, although to keep the proof simple we have to say
; what that value is.  And it leaves (mod k 11) clock ticks left.

(defthm fact-of-neg-at-loop-persists
  (implies (and (natp k)
                (integerp n)
                (< n 0)
                (acl2-numberp a))
           (equal (m1 (make-state 2 (list n a) nil *fact*)
                      (fact-of-neg-at-loop-clk k n a))
                  (m1 (make-state 2 (list (- n (floor k 11)) (a-value (floor k 11) n a)) nil *fact*)
                      (mod k 11)))))

; From the rule above we can prove that running from the top of the program (pc = 0)
; (fact-of-neg-clk k n) ticks, we reach a state that is NOT halted.

(defthm main-lemma
  (implies (and (natp k)
                (integerp n)
                (< n 0))
             (not (haltedp (m1 (make-state 0 (list n a) nil *fact*)
                               (fact-of-neg-clk k n)))))
  :rule-classes nil)

; Now we reveal that (fact-of-neg-clk k n) is, in fact, k.

(defthm fact-of-neg-at-loop-clk-revealed
  (equal (fact-of-neg-at-loop-clk k n a) k)
  :hints (("Goal" :in-theory (enable binary-clk+))))

(defthm fact-of-neg-fact-clk!-revealed
  (equal (fact-of-neg-clk k n) k)
  :hints (("Goal" :in-theory (enable binary-clk+))))

; And so we can use the main-lemma above to derive the desired result: if k is
; ANY natural number and n is a negative integer, then running k ticks from the
; initial state returns a state that is NOT halted.  That is, no k makes the
; program halt.

(defthm main
  (implies (and (natp k)
                (integerp n)
                (< n 0))
             (not (haltedp (m1 (make-state 0 (list n a) nil *fact*) k))))
  :hints (("Goal" :use main-lemma))
  :rule-classes nil)

; Now we use the inductive assertion proof to prove that pc 14 is unreachable if
; the input n is a negative integer.  This proof does not depend on anything
; that we prove above.

(defun n (s) (nth 0 (locals s)))
(defun a (s) (nth 1 (locals s)))

(defmacro defspec (name prog inputs pre-pc post-pc annotation-alist)
  (let ((Inv
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV")
          'run))
        (Inv-def
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV-DEF")
          'run))
        (Inv-opener
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV-OPENER")
          'run))
        (Inv-step
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV-STEP")
          'run))
        (Inv-run
         (intern-in-package-of-symbol
          (concatenate 'string (symbol-name name) "-INV-RUN")
          'run))
        (Correctness
         (intern-in-package-of-symbol
          (concatenate 'string "PARTIAL-CORRECTNESS-OF-PROGRAM-"
                       (symbol-name name))
          'run)))
    `(acl2::progn
      (acl2::defpun ,Inv (,@inputs s)
                    (if (member (pc s)
                                ',(strip-cars annotation-alist))
                        (and (equal (program s) ,prog)
                             (case (pc s)
                               ,@annotation-alist))
                        (,Inv ,@inputs (step s))))
      (defthm ,Inv-opener
        (implies (and (equal pc (pc s))
                      (syntaxp (quotep pc))
                      (not
                       (member pc
                               ',(strip-cars annotation-alist))))
                 (equal (,Inv ,@inputs s)
                        (,Inv ,@inputs (step s)))))
      (defthm ,Inv-step
        (implies (,Inv ,@inputs  s)
                 (,Inv ,@inputs (step s))))
      (defthm ,Inv-run
        (implies (,Inv ,@inputs s)
                 (,Inv ,@inputs (m1 s k)))
        :rule-classes nil
        :hints (("Goal" :in-theory (e/d (m1)(,Inv-def)))))
      (defthm ,Correctness
        (let* ((sk (m1 s0 k)))
          (implies
           (and (let ((s s0)) ,(cadr (assoc pre-pc annotation-alist)))
                (equal (pc s0) ,pre-pc)
                (equal (locals s0) (list* ,@inputs any))
                (equal (program s0) ,prog)
                (equal (pc sk) ,post-pc))
           (let ((s sk)) (declare (ignorable s)) ,(cadr (assoc post-pc annotation-alist)))))

        :hints (("Goal" :use
                 (:instance ,Inv-run
                            ,@(pairlis$ inputs (acl2::pairlis-x2 inputs nil))
                            (s s0)
                            (k k))))
        :rule-classes nil))))

(defspec fact *fact* (n0) 0 14
       ((0 (and (equal n0 (n s))
		(integerp n0)
                (< n0 0)))
	(2 (and (integerp n0)
                (< n0 0)
                (integerp (n s))
                (< (n s) 0)))
	(14 nil)))

(defthm pc-14-unreachable
  (implies (and (let ((s s0))
                  (and (equal n0 (n s))
                       (integerp n0)
                       (< n0 0)))
                (equal (pc s0) 0)
                (equal (locals s0) (list* n0 any))
                (equal (program s0) *fact*))
           (not (equal (pc (m1 s0 k)) 14)))
  :hints (("Goal" :use (:instance fact-inv-run (n0 n0)
                                  (s s0)
                                  (k k))))
  :rule-classes nil)
