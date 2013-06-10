; Correctness of Fact via Wormhole Abstraction

; Problem: Define an M1 program to compute the factorial of its natural number
; input.  Prove your program correct without specifying what happens to some
; variables.  Acknowledgement: This approach to code proofs was first developed
; by Dave Greve at Rockwell Collins Inc, who named the technique ``wormhole
; abstraction'' because the expressions defining the values of the variables we
; don't care about are hidden from sight.  In essence, wormhole abstraction
; characters the value of the uninteresting variables by saying ``they are what
; they are'' or ``their values are whatever the machine computes'' instead of
; characterizing them algebraically or extensionally.

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

(defun helper (n a)
  (if (zp n)
      a
      (helper (- n 1) (* n a))))

(defun fn (n) (helper n 1))

; (3) Prove that the algorithm satisfies the spec, by proving first that the
; helper is appropriately related to theta and then that fn is theta on ok
; inputs.

; Important Note: When you verify your helper function, you must consider the
; most general case.  For example, if helper is defined with formal parameters
; n and a and fn calls helper initializing a to 0, your helper theorem must
; be about (helper n a), not just about the special case (helper n 0).

(defthm helper-is-theta
  (implies (and (ok-inputs n)
                (natp a))
           (equal (helper n a)
                  (* a (theta n)))))

(defthm fn-is-theta
  (implies (ok-inputs n)
           (equal (fn n)
                  (theta n))))

; Disable these two lemmas because they confuse the theorem prover when it is
; dealing with the code versus fn.

(in-theory (disable helper-is-theta fn-is-theta))

; (4) Write your M1 program with the intention of implementing your algorithm.
; This program implements fact a little oddly: it uses a temporary variable,
; local 2, that is otherwise unimportant.

(defconst *pi*
  '((iconst 1)  ;  0
    (istore 1)  ;  1
    (iload 0)   ;  2
    (ifeq 12)   ;  3
    (iload 0)   ;  4
    (istore 2)  ;  5
    (iload 0)   ;  6
    (iconst 1)  ;  7
    (isub)      ;  8
    (istore 0)  ;  9
    (iload 2)   ; 10
    (iload 1)   ; 11
    (imul)      ; 12
    (istore 1)  ; 13
    (goto -12)  ; 14
    (iload 1)   ; 15
    (halt))     ; 16
  )

; (5) Define the ACL2 function that clocks your program, starting with the
; loop clock and then using it to clock the whole program.  The clock
; should take the program from pc 0 to a HALT statement.  (Sometimes your
; clocks will require multiple inputs or other locals, but our example only
; requires the first local.)

(defun loop-clk (n)
  (if (zp n)
      3
      (clk+ 13
            (loop-clk (- n 1)))))

(defun clk (n)
  (clk+ 2
        (loop-clk n)))

; (6) Prove that the code implements your algorithm, starting with the lemma
; that the loop implements the helper.  Each time you prove a lemma relating
; code to algorithm, disable the corresponding clock function so the theorem
; prover doesn't look any deeper into subsequent code.

; Important Note: Your lemma about the loop must consider the general case.
; For example, if the loop uses the locals n and a, you must characterize
; its behavior for arbitrary, legal n and a, not just a special case (e.g.,
; where a is 0).

(defun poised-to-loop (n s)
  (and (acl2::true-listp s)
       (equal (len s) 4)
       (equal (pc s) 2)
       (equal (program s) *pi*)
       (equal n (nth 0 (locals s)))
       (natp n)
       (natp (nth 1 (locals s)))))

(defun loop-hint (n s)
  (if (zp n)
      (list n s)
      (loop-hint (- n 1)
                 (m1 s 13))))

(defthm about-make-state
  (and (acl2::true-listp (make-state pc locs stk prog))
       (equal (len (make-state pc locs stk prog)) 4))
  :hints (("Goal" :in-theory (enable make-state))))


(defun fact-loop-locals (n s)
  (locals (m1 s (loop-clk n))))

(defthm fact-loop-thm
  (implies (poised-to-loop n s)
           (equal (m1 s (loop-clk n))
                  (make-state 16
                              (if (zp n)
                                  (locals s)
                                  (update-nth 2
                                              1
                                              (fact-loop-locals n s)))
                              (push (helper (nth 0 (locals s))
                                            (nth 1 (locals s)))
                                    (stack s))
                              *pi*)))
  :hints (("Goal" :induct (loop-hint n s))))

(in-theory (disable loop-clk fact-loop-locals))

(defun poised-for-fact (n s)
  (and (acl2::true-listp s)
       (equal (len s) 4)
       (equal (pc s) 0)
       (equal (program s) *pi*)
       (equal n (nth 0 (locals s)))
       (natp n)))

(defun fact-locals (n s)
  (locals (m1 s (clk n))))

(defthm fact-thm
  (implies (poised-for-fact n s)
           (equal (m1 s (clk n))
                  (make-state 16
                              (fact-locals n s)
                              (push (fn (nth 0 (locals s)))
                                    (stack s))
                              *pi*))))

(in-theory (disable clk fact-locals))

; (7) Put the two steps together to get correctness.

(in-theory (enable fn-is-theta))

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
                       (! n))))
  :rule-classes nil)

