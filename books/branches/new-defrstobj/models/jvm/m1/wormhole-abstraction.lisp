; Correctness of Fact via Wormhole Abstraction

; Problem: Define an M1 program to compute the factorial of its natural number
; input.  Prove your program correct without specifying what happens to some
; variables.

; Acknowledgement: This approach to code proofs was first developed by Dave
; Greve at Rockwell Collins Inc, who named the technique ``wormhole
; abstraction'' because the expressions defining the values of the variables we
; don't care about are hidden from sight.  In essence, wormhole abstraction
; characterizes the value of the uninteresting variables by saying ``they are
; what they are'' or ``their values are whatever the machine computes'' instead
; of characterizing them algebraically or extensionally.

; This file started as fact.lisp.  But I modified the program to be verified so
; that it unnecessarily changes local variable 2 (in addition to locals 0 and
; 1).  Then I verified the program without explicitly characterizing how local
; variable 2 -- or any other local -- changes.  If you attempt to verify this
; program by the method used to verify fact.lisp, you'll see that you must
; specify what is happening to local 2 even though it is not needed to express
; the final answer.  I have put comments beginning with the tag "Wormhole
; Abstraction" everywhere I changed fact.lisp below.

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

; Wormhole Abstraction: This program implements fact a little oddly: it uses a
; temporary variable, local 2, that is otherwise unimportant.  This change is not
; illustrative of wormhole abstraction per se.  It just makes this program more
; typical of the situations in which wormhole abstraction is useful:  when a program
; side-effects many machine resources on the way to computing what really matters and
; you don't want to have to specify all those side-effects explicitly.

(defconst *pi*
  '((iconst 1)  ;  0
    (istore 1)  ;  1
    (iload 0)   ;  2
    (ifeq 12)   ;  3
    (iload 0)   ;  4
    (istore 2)  ;  5  ; Wormhole Abstraction: Note that local 2 takes on
    (iload 0)   ;  6  ; successive values of local variable 0.
    (iconst 1)  ;  7
    (isub)      ;  8
    (istore 0)  ;  9
    (iload 2)   ; 10  ; Wormhole Abstraction: And local 2 is used in the
    (iload 1)   ; 11  ; calculation of the answer, local 1.
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
      (clk+ 13  ; Wormhole Abstraction: The clock is a little different for
                ; this version of the program since we execute two extra
                ; instructions.  the program in fact.lisp took 11 steps here
                ; instead of 13.  Again, this is not illustrative of wormhole
                ; abstraction but is a change from fact.lisp.

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

; Wormhole Abstraction: We now illustrate wormhole abstraction.  The key step
; in any code proof about a program with a single loop is the lemma that
; characterizes how the loop affects the machine's resources.  (In fact.lisp we
; called that lemma ``loop-is-helper'' and it is given that name below too.)
; The utility of wormhole abstraction is most apparent in the statement and
; proof of this crucial lemma because it is during the proof of this lemma that
; we spend the most time ``walking through the code'' and tracking
; side-effects.

; The key idea in wormhole abstraction is that we are do not want to specify
; EXPLICITLY how some of the machine resources variables are changed as the
; program executes or what their final values are.  In this example, we'll
; focus on the changes to the local variables.  We're just going to say ``the
; final locals are whatever M1 computes them to be.''  For succinctness we
; define this concept:

(defun fact-loop-locals (n s)
  (locals (m1 s (loop-clk n))))

; Assume, above, that n is the natural number on which we're to compute
; factorial and s is a state poised at the top of the loop (pc = 2) of program
; *pi*.  Then (fact-loop-locals n s) is the final value of the local variables
; after the M1 machine has run as long as the clock says to run.  Notice that
; this definition does not explicitly characterize the values of any of the
; locals!  They are whatever the code tells M1 to compute.

; Wormhole Abstraction: It is convenient to wrap up the conditions, above, on n
; and s as a named concept.

(defun poised-to-loop (n s)
  (and (natp n)
       (equal (pc s) 2)
       (equal (program s) *pi*)
       (equal n (nth 0 (locals s)))))

; Wormhole Abstraction: In fact.lisp we assumed we were dealing with a state
; whose locals were (list n a) and we characterized the final answer in a to be
; (helper n a).  This had a powerful but very subtle effect on ACL2's behavior:
; it suggested to ACL2 that it should induct on n and a in the way that (helper
; n a) recurs.  That suggestion will no longer be part of our statement of the
; theorem.  So we have to tell ACL2 what to induct on.  But we're going to
; employ wormhole abstraction here too and say ``induct on the way M1 is driven
; around the loop by whatever code it is running.''

(defun loop-hint (n s)
  (if (zp n)
      (list n s)
      (loop-hint (- n 1)
                 (M1 s 13))))

; The value of the function loop-hint is unimportant.  What is important is how
; loop-hint recurs.  Notice that it tests whether (zp n) is true or not.  If
; true, it terminates in a base case (no recursive calls).  Otherwise, it
; replaces n by (- n 1) and s by (M1 s 13).  We will be assuming that n and s
; satisfy (poised-to-loop n s).

; When we ask ACL2 to prove the crucial lemma we will give the
;   :hints (("Goal" :induct (loop-hint n s)))

; This tells ACL2 to induct the way (loop-hint n s) recurs.  If the goal is to
; prove (psi n s), then ``induct the way (loop-hint n s) recurs'' means"

; Base Case:        (zp n) --> (psi n s)

; Induction Step:   [(not (zp n)) & (psi (- n 1) (M1 s 13))] --> (psi n s)

; Note that we haven't told ACL2 to replace local 1 by the product of local 0
; and local 1, and we haven't told it to replace local 2 by local 1.  (We have
; told it, implicitly to replace local 0 by the result of decrementing local 0
; by 1, by virtue of telling it to replace n by n-1 and requiring that n be
; local 0.)  Instead of being explicit, we just tell the induction mechanism to
; symbolically run the code 13 steps from the top of the loop and use whatever
; new state is produced.  That state is just the state you get by going once
; around the loop.

; Wormhole Abstraction: We also make a minor technical adjustment to the rule
; configuration used in fact.lisp: we disable the functions NTH and UPDATE-NTH
; so that terms like (NTH 1 (locals s)) and (UPDATE-NTH 2 v (locals s)) just
; stay in that form.  We also disable NTH-ADD1! which is a :rewrite rule that
; would otherwise expand (NTH 1 (locals s)) to (NTH 0 (cdr (locals s))) and
; thence to (cadr (locals s)).  We will be exploiting the standard rules like
; NTH-UPDATE-NTH to simplify such terms as:

; (NTH 1 (UPDATE-NTH 2 v (locals s))) = (NTH 1 (locals s)).

(in-theory (disable nth update-nth nth-add1!))

; Why are we doing this for Wormhole Abstraction and not for our other proofs?
; Because in our other proofs we describe the locals as (list n a) or other
; [semi-] explicit cons structures and so we wanted our rules to reduce NTH and
; UPDATE-NTH on such structures.  Now we don't.  Note that in this setting we
; do not even know how many locals are allocated (i.e., what is the length of
; (locals s)).

; Wormhole Abstraction: Here is the crucial lemma: If s is a state poised to
; execute at the top of the loop of the factorial program on input n, and we
; run s (loop-clk n) steps, we get a state where the final pc is 16, the locals
; are whatever they are, and the stack has (helper (nth 0 (locals s)) (nth 1
; (locals s))) on top of whatever was there before.  Note that we do not say --
; explicitly -- what the final locals are.  They are what they are.

(defthm loop-is-helper
  (implies (poised-to-loop n s)
           (equal (m1 s (loop-clk n))
                  (make-state 16
                              (fact-loop-locals n s)
                              (push (helper (nth 0 (locals s))
                                            (nth 1 (locals s)))
                                    (stack s))
                              *pi*)))
  :hints (("Goal" :induct (loop-hint n s))))

; Contrast this to the original version of the lemma in fact.lisp:

; (defthm loop-is-helper          ; [from fact.lisp]
;   (implies (and (ok-inputs n)
;                 (natp a))
;           (equal (m1 (make-state 2
;                                  (list n a)
;                                  nil
;                                  *pi*)
;                      (loop-clk n))
;                  (make-state 14
;                              (list 0 (helper n a))
;                              (push (helper n a) nil)
;                              *pi*))))

; Note that in the original, which did not involve local 2, we characterized
; explicitly every component of the final state, e.g., that local 0 is 0, that
; local 1 is given by (helper n a), etc.  Had the original program involved
; changes to local 2 we would have had to give them explicitly.  Wormhole
; abstraction is a way to write and prove such lemmas without being explicit
; about the final values of some variables.  ``They are what they are.''

; Wormhole Abstraction:  Now following the original pattern, we disable the clock
; for the loop but we also disable the function that computes the final value of
; the locals.  The idea is simply not to concern ourselves any more with those
; concepts.

(in-theory (disable loop-clk fact-loop-locals))

; We apply the same wormhole abstraction techniques to the next step, from pc 0 to
; to the top of the loop and then on to the HALT:

(defun poised-for-fact (n s)
  (and (natp n)
       (equal (pc s) 0)
       (equal (program s) *pi*)
       (equal n (nth 0 (locals s)))))

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

; Wormhole Abstraction: In the original fact.lisp we proved PROGRAM-CORRECT
; before finishing with the same TOTAL-CORRECTNESS theorem shown below.  Recall
; PROGRAM-CORRECT just replaced our operational model of the final value, (fn
; n) by its specification value (! n).  It also explicated all the other state
; changes; we then used TOTAL-CORRECTNESS just to exhibit the ones we care
; about.  We could do something similar here but don't bother.  Instead we just
; exhibit the desired total correctness theorem.  This is the same
; TOTAL-CORRECTNESS formula proved before, without ever characterizing the
; local variables beyond ``they are what they are.''

; Note however that we have to enable NTH below.  Why?  To answer that,
; consider the state to which we apply M1 below.  It contains the list
; structure (list n) as its locals.  We need to know that this state satisfies
; the poised-for-fact predicate.  That means we need to be able to show that
; (nth 0 (list n)) is n.  That can be arranged by enabling NTH.

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
  :hints (("Goal" :in-theory (enable nth)))
  :rule-classes nil)

; An alternative version, more in keeping with the style we've adopted here, is
; to refrain from describing the locals with a cons structure and just
; hypothesize that the 0th local is n:

(defthm alternative-total-correctness
  (implies (and (natp n)
                (equal n (nth 0 locals))
                (equal sf (m1 (make-state 0
                                          locals
                                          nil
                                          *pi*)
                              (clk n))))
           (and (equal (next-inst sf) '(HALT))
                (equal (top (stack sf))
                       (! n))))
  :rule-classes nil)

