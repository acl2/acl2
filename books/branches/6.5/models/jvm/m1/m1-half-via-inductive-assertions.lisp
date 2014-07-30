; Correctness of Fact

; Problem: Define an M1 program to halve its integer input, at least when that
; input is even.  Prove that the if the program reaches its HALT then the input
; was even and the correct answer is left on the stack.

; Design Plan: I will count n down to 0 by 2 and increment an accumulator, a,
; initially 0.

; Proof Plan: I will use the inductive assertion method described in ``Inductive
; Assertions and Operational Semantics,'' J Strother Moore, CHARME 2003, D. Geist
; (ed.), Springer Verlag LNCS 2860, pp. 289-303, 2003, the long version of which
; can be found here:

; http://www.cs.utexas.edu/users/moore/publications/trecia/long.pdf

; That paper illustrates the technique on the M5 model of the JVM.  This is a
; recapitulation of that same script, except for M1.  In this book I actually
; do the proof twice.  The first time I transcribe the events in Sections 4
; through 9 of that paper.  Then I define the macro described in Section 10 of
; that paper and invoke the macro, which automatically does all of the events
; in Sections 4--9, with slightly different names to avoid redundancy.

; In this presentation I only give the section headers of the various sections
; and provide no commentary, since the paper is self-explanatory.  However,
; because the M5 model is different from M1, some things have changed.  Three
; differences manifest themselves: M5 supports only 32-bit integers and so the
; assertions in the paper have to accommodate that limitation; M1 supports
; unbounded integers.  M5 supports threads and the theorem proved in the paper
; limits the execution trace to a single active thread; M1 is a uniprocessor.
; And sthe program counter on M5 counts bytes whereas on M1 it counts
; instructions, so some of the program counters mentioned are different than
; those in the paper, e.g., the HALT is at pc 17 in the paper but at pc 14
; here.  Finally, the program verified in the paper leaves the final answer in
; local 1, whereas here I chose to push it onto the stack, for uniformity with
; the other M1 programs verified in this collection.

; (0) Start ACL2
; (include-book "m1")

(in-package "M1")

; Section 4:  An Iterative Program

(defconst *pi*
  '((ICONST 0) ; 0
    (ISTORE 1) ; 1 a := 0
    (ILOAD 0)  ; 2 top of loop:
    (IFEQ 10)  ; 3 if n=0, goto 13
    (ILOAD 1)  ; 4
    (ICONST 1) ; 5
    (IADD)     ; 6
    (ISTORE 1) ; 7 a := a+1
    (ILOAD 0)  ; 8
    (ICONST 2) ; 9
    (ISUB)     ;10
    (ISTORE 0) ;11 n := n-2
    (GOTO -10) ;12 goto top of loop
    (ILOAD 1)  ;13
    (HALT)))   ;14 ``return'' a

; Here is a paraphrase of our goal theorem.  Let s0 be an M1 state in which the
; initial value, n0, of n (i.e., local 0) is some natural number, pc is 0, and
; the program is *pi*.  Let sk be any state reachable from s0, i.e., (m1 s0 k)
; for any k.  Suppose the pc in sk is 14.  Then n0 is even and the value on top
; of the stack is n0/2.  Formally:

;   (let* ((sk (m1 s0 k)))
;     (implies (and (let ((s s0))
;                     (and (equal (n s) n0)
;                          (integerp n0)
;                          (<= 0 n0)))
;                   (equal (pc s0) 0)
;                   (equal (locals s0) (list* n0 any))
;                   (equal (program s0) *pi*)
;                   (equal (pc sk) 14))
;              (let ((s sk))
;                (and (evenp n0)
;                     (equal (top (stack s)) (/ n0 2))))))



; Section 5:  The Assertions at the Three Cut Points

(defun P (n0 n) ; Pre-Condition
  (and (equal n n0)
       (integerp n0)
       (<= 0 n0)))

(defun R (n0 n a) ; Loop Invariant
  (and (integerp n0)
       (<= 0 n0)
       (integerp n)
       (if (and (<= 0 n)
                (integerp a)
                (evenp n))
           (equal (+ a (/ n 2))
                  (/ n0 2))
           (not (evenp n)))
       (iff (evenp n0) (evenp n))))

(defun Q (n0 tos) ; Post-Condition
  (and (evenp n0)
       (equal tos (/ n0 2))))

; Section 6:  The Verification Conditions

; Discussion only, no events.

; Section 7:  Attaching the Assertions to the Code

(defun n (s) (nth 0 (locals s)))
(defun a (s) (nth 1 (locals s)))

(defun assertion (n0 s)
  (let ((n (n s))
        (a (a s)))
    (and (equal (program s) *pi*)
         (case (pc s)
           (0 (P n0 n))
           (2 (R n0 n a))
           (14 (Q n0 (top (stack s))))
           (otherwise nil)))))

; Section 8:  The Nugget: Defining the Invariant

(include-book "misc/defpun" :dir :system)

(acl2::defpun Inv (n0 s)
  (if (member (pc s) '(0 2 14))
      (assertion n0 s)
      (Inv n0 (step s))))

; Because the paper presents a proof at the level a human might do one, it does
; not include the ACL2-specific events needed to drive the prover to that
; proof.  There is only one such lemma required here and that is a rewrite rule
; that forces the (Inv n0 s) to expand to (Inv n0 (step s)) if the pc is not
; one of the annotated ones.  That strategy is made clear in the proof
; described in the paper.  Here is how it is communicated to ACL2.

(defthm inv-opener
  (implies (and (equal pc (pc s))
                (syntaxp (quotep pc))
                (not (member pc '(0 2 14))))
           (equal (inv n0 s)
                   (inv n0 (step s)))))

; Section 9:  Proofs

(defthm inv-step                  ; called Property-1-of-Inv in the paper
  (implies (inv n0 s)
           (inv n0 (step s))))

(defthm inv-run                   ; called Property-4-of-Inv in the paper
  (implies (inv n0 s)
           (inv n0 (m1 s k)))
  :rule-classes nil
  :hints (("goal" :in-theory (e/d (m1) (inv-def)))))

(defthm Corollary-1              ; called Corollary-1 in the paper
  (implies (and (equal n0 (n s0))
                (integerp n0)
                (<= 0 n0)
                (equal (pc s0) 0)
                (equal (locals s0) (list* n0 any))
                (equal (program s0) *pi*)
                (equal sk (M1 s0 k))
                (equal (pc sk) 14))
           (and (evenp n0)
                (equal (top (stack sk)) (/ n0 2))))
  :hints (("Goal" :use (:instance inv-run (s s0) (n0 n0))))
  :rule-classes nil)


; Section 10:  Packaging It Up

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
           (let ((s sk)) ,(cadr (assoc post-pc annotation-alist)))))

        :hints (("Goal" :use
                 (:instance ,Inv-run
                            ,@(pairlis$ inputs (acl2::pairlis-x2 inputs nil))
                            (s s0)
                            (k k))))
        :rule-classes nil))))

(defspec pi *pi*  (n0) 0 14
  ( ; Pre-Condition:
   (0 (and (equal (n s) n0)
           (integerp n0)
           (<= 0 n0)))

; Loop Invariant:
   (2 (and (integerp n0)
           (<= 0 n0)
           (integerp (n s))
           (if (and (<= 0 (n s))
                    (integerp (a s))
                    (evenp (n s)))
               (equal (+ (a s) (/ (n s) 2))
                      (/ n0 2))
               (not (evenp (n s))))
           (iff (evenp n0) (evenp (n s)))))

; Post-condition:
   (14 (and (evenp n0)
            (equal (top (stack s)) (/ n0 2))))))

; If you print the last event proved by this command, you will see that it is
; logically equivalent to Corollary-1 above, the desired result about our program.

; M1 !>:pe PARTIAL-CORRECTNESS-OF-PROGRAM-PI
;           16:x(DEFSPEC PI *PI* ...)
;               \
; >              (DEFTHM
;                 PARTIAL-CORRECTNESS-OF-PROGRAM-PI
;                 (LET* ((SK (M1 S0 K)))
;                       (IMPLIES (AND (LET ((S S0))
;                                          (AND (EQUAL (N S) N0)
;                                               (INTEGERP N0)
;                                               (<= 0 N0)))
;                                     (EQUAL (PC S0) 0)
;                                     (EQUAL (LOCALS S0) (LIST* N0 ANY))
;                                     (EQUAL (PROGRAM S0) *PI*)
;                                     (EQUAL (PC SK) 14))
;                                (LET ((S SK))
;                                     (AND (EVENP N0)
;                                          (EQUAL (TOP (STACK S)) (/ N0 2))))))
;                 :HINTS (("Goal" :USE (:INSTANCE PI-INV-RUN (N0 N0)
;                                                 (S S0)
;                                                 (K K))))
;                 :RULE-CLASSES NIL)

; The use of LET* and LET are just convenient ways for the macro to manipulate
; the user's specification, which is in terms of the state variable s instead
; of s0 and sk.

