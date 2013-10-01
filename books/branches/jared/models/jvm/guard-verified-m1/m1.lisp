#||

The M1 Model
J Strother Moore

See the README file on this directory for an overview of this work.  In this
file I define the M1 model -- a very simple machine sort of kinda like the JVM.
The machine has nine instructions that manipulate an array of local variable
values and a push down stack.

HOW TO PLAY WITH AND RECERTIFY THIS FILE

If you are playing with this model, do this:

; (include-book "good-statep")

; (ld "m1.lisp" :ld-pre-eval-print t)

But to recertify it, do:

; (include-book "good-statep")

; (certify-book "m1" 1)

BRIEF INTRODUCTION TO GUARDS

In the definitions below we include ``guards'' for the functions we define.
The guards for a function tell us what to expect of the arguments whenever the
function is called.  For example, consider this definition which appears below:

 (defun top (stack)
  (declare (xargs :guard (and (stackp stack)
                              (not (endp stack)))))
  (car stack))

Logically speaking, this just gives us the axiom that (top stack) is
 (car stack), i.e.,

 Axiom:
 (equal (top stack) (car stack))

We call this the ``logical'' definition of top and it is all that matters about
top when we are proving theorems.

But operationally it also tells us that we ``expect'' stack to satisfy the
predicate stackp and to be non-empty.

Why express these expectations?  First, as with type declarations in many
programming languages, it is sometimes helpful while reading a definition to
know what kind of things the definition deals with.  More importantly, by
expressing our expectations formally we can carry out a kind of ``sanity
check'' on the model: are all our expectations met when we run the model on
concrete data?  For example, if some other function, e.g., execute-IADD below,
calls top, we can try to prove -- with the theorem prover -- that the guards
for execute-IADD imply the guards for top, i.e., that execute-IADD is using top
in compliance with our expectations for top.  This process -- of proving that
every call of every function is on arguments that meet our expectations -- is
called ``guard verification.''  Third, guards allow us to run this model faster
on concrete data.  If we have proved that all guards are satisfied, then when
we run the model we just have to check that the top-level input satisfies the
expressed expectations for the top-level function call and then we can know --
without any runtime checking -- that every other call of every function in the
model is on the expected kind of data.  That in turn means we can compile the
functions without checking the expectations.  For the stack function top it
means that the compiled code for top need not check that its argument is a
non-empty stack: it just calls car exactly as the axiom says.

We will verify all the guards below in a later book, verify-guards.lisp.  For
the moment, I recommend just noting the guards as a way of learning what we
expect about the arguments, without

Some functions (e.g., nth below) are defined redundantly with those in
good-statep.lisp but are included here to make this file a self-contained
explication of the unguarded (logical) definition of M1.

||#

(in-package "M1")

; For current purposes, guards may be ignored.

(set-verify-guards-eagerness 0)

; Note: The command above tells ACL2 not to bother to verify the guards on
; these functions.  This is in line with my advice about not paying too much
; attention to the guards upon the first reading.  But there is more to it than
; that.  Some of the guards CANNOT be verified without first introducing the
; logical definitions and proving properties of them.  Thus, it is actually
; necessary to take this two-step approach.

; -----------------------------------------------------------------
; Stack Manipulation

(defun push (x y)
  (declare (xargs :guard t))
  (cons x y))

(defun top (stack)
  (declare (xargs :guard (and (stackp stack)
                              (not (endp stack)))))
  (car stack))

(defun pop (stack)
  (declare (xargs :guard (and (stackp stack)
                              (not (endp stack)))))
  (cdr stack))

; -----------------------------------------------------------------

; Indexing into a List:

; We will fetch the nth element of a list with the funciton nth and
; update it with the function update-nth.  These two functions are
; defined in the ACL2 sources.  You can look at their
; definitions by typing

; ACL2 !>:pe nth
; or
; ACL2 !>:pe update-nth

; You may think of NTH and UPDATE-NTH as being defined this way (their ACL2
; definitions are syntactically different but semantically equivalent):

; (DEFUN NTH (N L)
;   (IF (ZP N)
;       (CAR L)
;       (NTH (- N 1) (CDR L))))
; and
; (DEFUN UPDATE-NTH (N V L)
;   (IF (ZP N)
;       (CONS V (CDR L))
;       (CONS (CAR L)
;             (UPDATE-NTH (1- N) V (CDR L)))))

; Note that if n is ``too big'' then the definitions above will apply car and
; cdr to nil.  However, in Lisp, (car nil) = (cdr nil) = nil.

;   (nth 3 '(A B))
; = (nth 2 '(B))
; = (nth 1 NIL)
; = (nth 0 (cdr nil))
; = (car (cdr nil))
; = nil

; and

;   (update-nth 3 44 '(A B))
; = (cons 'A (update-nth 2 44 '(B)))
; = (cons 'A (cons 'B (update-nth 1 44 nil)))
; = (cons 'A (cons 'B (cons (car nil) (update-nth 0 44 (cdr nil)))))
; = (cons 'A (cons 'B (cons nil (cons 44 nil))))
; = '(A B nil 44)

; -----------------------------------------------------------------

; State Manipulation:

(defun make-state (pc locals stack program)
  (declare (xargs :guard t))
  (cons pc
        (cons locals
              (cons stack
                    (cons program
                          nil)))))

(defun pc (s)
  (declare (xargs :guard (true-listp s)))
  (nth 0 s))
(defun locals (s)
  (declare (xargs :guard (true-listp s)))
  (nth 1 s))
(defun stack (s)
  (declare (xargs :guard (true-listp s)))
  (nth 2 s))
(defun program (s)
  (declare (xargs :guard (true-listp s)))
  (nth 3 s))

; -----------------------------------------------------------------
; Instruction Accessors

(defun op-code (inst)
  (declare (xargs :guard (true-listp inst)))
  (nth 0 inst))

(defun arg1 (inst)
  (declare (xargs :guard (true-listp inst)))
  (nth 1 inst))

; These next two are irrelevant to M1 but are included in the model to
; to allow us to extend it conveniently with new instructions.

(defun arg2 (inst)
  (declare (xargs :guard (true-listp inst)))
  (nth 2 inst))

(defun arg3 (inst)
  (declare (xargs :guard (true-listp inst)))
  (nth 3 inst))

; -----------------------------------------------------------------
; The Next Instruction

(defun next-inst (s)
  (declare (xargs :guard (and (true-listp s)
                              (natp (pc s))
                              (true-listp (program s)))))
  (nth (pc s) (program s)))

; -----------------------------------------------------------------

; The M1 Machine

; Now we define the semantics of each instruction.  These functions are called
; ``semantic functions.''

; Each opcode will be given semantics with an ACL2 function that takes an
; instruction (with the given opcode) and a state and returns the state
; produced by executing the instruction.  For example, the ILOAD instruction,
; looks like this:

; (ILOAD k)

; where k is the index of some local variable.  Informally, the instruction
; extracts the value of local variable k from the state and pushes that value
; onto the stack in the state.  The instruction also advances the program
; counter.  Formally, this transformation on the state is specified by the
; function execute-ILOAD, below.  Execute-ILOAD is called the ``semantic
; function'' for ILOAD.  We define the instruction set by defining a semantic
; function for each opcode in it.

; Our expectation when (execute-ILOAD inst s) is called is that s is a ``good''
; M1 state, that inst is the next instruction in s, and that inst is an ILOAD
; instruction. Because we have analogous expectations on the semantic function
; for each opcode, we wrap up these expectations into a single predicate:

(defun ok-to-step (op inst s)
  (declare (xargs :guard t))
  (and (good-statep s)
       (equal inst (next-inst s))
       (equal (op-code inst) op)))

; The predicate ok-to-step is only used to express the guards on our semantic
; functions.

; Exactly what a ``good'' state is is defined in the file good-state.lisp, but
; I do not recommend reading it yet, if at all!  The only reason to read it is
; to learn about bytecode verification.  Why?  What does good-statep mean?
; Aside from the obvious ``shape'' constraints on s, it expresses a fairly
; sophisticated constraint on what constitutes a well-formed M1 program in
; state s.  Most of that is straightforward, e.g., each instruction has the
; right syntax, e.g., the ILOAD instruction has a local variable number as its
; argument.  But there are some subtlties.  One is that the program counter
; never gets outside of the program.  So every jump has to be to a legal pc.
; Another is that any instruction that manipulates the local variables must
; find the local variable array sufficiently long; it is illegal to reference
; local variable 5 if there are only 4 local variable values in the state.  But
; the most subtle is that any instruction that pops the stack will always find
; enough items on the stack.  Since instructions can push and pop items, this
; last constraint is not a local one but depends on the control flow from one
; instruction to another.  All these conditions are checked by a predicate akin
; to the Java bytecode verifier.  That predicate involves the construction of a
; ``stack map'' that says how deep the stack gets as the execution proceeds
; through the program.  That's all we'll say about ``good'' states here.

; But recall the little introduction to guards above: if the guards for
; execute-ILOAD are satisfied, we can run execute-ILOAD without error, i.e.,
; without worrying whether the instruction is well-formed, whether the local
; variable of that index exists, whether incrementing the pc pushes it outside
; the bounds of the program, etc.  So, if you're willing to assume our
; expressed expectations are met, all you really need to know is what each
; instruction does.  So now we list the instructions and give an informal and
; then a formal description of their semantics.


; Semantics of (ILOAD k): increment the pc and push onto the stack the value of
; the kth local.  Aside: We will know, by guard verification, that the new pc
; is legal and that the value pushed is a rational number.  As a rule, I will
; not comment here on everything we know by guard verification, I'm just trying
; to give you a sense of the implications of our expectations.

(defun execute-ILOAD (inst s)
  (declare (xargs :guard (ok-to-step 'ILOAD inst s)))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (nth (arg1 inst)
                         (locals s))
                    (stack s))
              (program s)))


; Semantics of (ICONST k):  increment the pc and push k onto the stack.

(defun execute-ICONST (inst s)
  (declare (xargs :guard (ok-to-step 'ICONST inst s)))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (arg1 inst) (stack s))
              (program s)))

; Semantics of (IADD): increment the pc, pop two items off the stack and push
; their sum.  Aside: We will know, by guard verification, that there are at
; least two items on the stack and that they are both rational numbers.

(defun execute-IADD (inst s)
  (declare (xargs :guard (ok-to-step 'IADD inst s))
           (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (+ (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

; Semantics of (ISUB): increment the pc, pop two items off the stack and push
; their difference.

(defun execute-ISUB (inst s)
  (declare (xargs :guard (ok-to-step 'ISUB inst s))
           (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (- (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

; Semantics of (IMUL): increment the pc, pop two items off the stack and push
; their product.

(defun execute-IMUL (inst s)
  (declare (xargs :guard (ok-to-step 'IMUL inst s))
           (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (* (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

; Semantics of (ISTORE k): increment the pc, pop one item off the stack, and
; store it as the value of local variable k.

(defun execute-ISTORE (inst s)
  (declare (xargs :guard (ok-to-step 'ISTORE inst s)))
  (make-state (+ 1 (pc s))
              (update-nth (arg1 inst) (top (stack s)) (locals s))
              (pop (stack s))
              (program s)))

; Semantics of (GOTO k): increment the pc by k.  Aside: We will know, by guard
; verification, that the new pc is legal.

(defun execute-GOTO (inst s)
  (declare (xargs :guard (ok-to-step 'GOTO inst s)))
  (make-state (+ (arg1 inst) (pc s))
              (locals s)
              (stack s)
              (program s)))

; Semantics of (IFEQ k): pop one item off the stack and increment the pc k if
; that item is 0 and by 1 if if is non-0.  Aside: We will know, by guard
; verification, that the new pc is legal.

(defun execute-IFEQ (inst s)
  (declare (xargs :guard (ok-to-step 'IFEQ inst s)))
  (make-state (if (equal (top (stack s)) 0)
                  (+ (arg1 inst) (pc s))
                (+ 1 (pc s)))
              (locals s)
              (pop (stack s))
              (program s)))

(defun do-inst (inst s)
  (declare (xargs :guard (and (good-statep s)
                              (equal inst (next-inst s)))))
  (if (equal (op-code inst) 'ILOAD)
      (execute-ILOAD  inst s)
      (if (equal (op-code inst) 'ICONST)
          (execute-ICONST  inst s)
          (if (equal (op-code inst) 'IADD)
              (execute-IADD   inst s)
              (if (equal (op-code inst) 'ISUB)
                  (execute-ISUB   inst s)
                  (if (equal (op-code inst) 'IMUL)
                      (execute-IMUL   inst s)
                      (if (equal (op-code inst) 'ISTORE)
                          (execute-ISTORE  inst s)
                          (if (equal (op-code inst) 'GOTO)
                              (execute-GOTO   inst s)
                              (if (equal (op-code inst) 'IFEQ)
                                  (execute-IFEQ   inst s)
                                  s)))))))))

; This is the single-step function: it executes the next instruction in a
; state.  Aside: We will know, by guard verification, that the resulting state
; is a good state.

(defun step (s)
     (declare (xargs :guard (good-statep s)))
     (do-inst (next-inst s) s))

(defun m1 (s n)
  (declare (xargs :guard (and (good-statep s)
                              (natp n))))
  (if (zp n)
      s
      (m1 (step s) (- n 1))))

(defun haltedp (s)
  (declare (xargs :guard (good-statep s)))
  (equal (next-inst s) '(HALT)))

; That's all there is to M1.  The rest of this file sets up some stuff
; we'll need to prove theorems about M1 programs.  But I recommend that
; you play with M1 instead.  For example, write and run some M1 programs.
; Challenge yourself.  Can you write a program to multiply two number togther
; without using the IMUL instructions?  Can you write a program to sum the
; naturals from n down to 0?  Can you write a program to divide one number by
; another?

; One way to test your programs is just to run the M1 model on sample data.
; For example, here is a program to multiply the first two locals together,
; without using IMUL.  Below I let the initial state, s_i, be a state that is
; poised to multiply 7 times 9.  Then I let the final state, s_f, be the result
; of running s_i for 82 steps.  Then I check that s_i and s_f are both good
; states, that s_f is halted, and that 7*9 is on top of the stack in s_f.


#||
 (let* ((s_i (make-state 0              ; pc = 0 ;
                         '(7 9 0)       ; locals x, y, and a ;
                         nil            ; stack = nil ;
                                       ; program: ;
                                       ;  pc   pseudo-code ;
                         '((ICONST 0)   ;   0 ;
                           (ISTORE 2)   ;   1  a = 0; ;
                           (ILOAD 0)    ;   2  [loop:] ;
                           (IFEQ 10)    ;   3  if x=0 then go to end; ;
                           (ILOAD 0)    ;   4 ;
                           (ICONST 1)   ;   5 ;
                           (ISUB)       ;   6 ;
                           (ISTORE 0)   ;   7  x = x-1; ;
                           (ILOAD 1)    ;   8 ;
                           (ILOAD 2)    ;   9 ;
                           (IADD)       ;  10 ;
                           (ISTORE 2)   ;  11  a = y+a; ;
                           (GOTO -10)   ;  12  go to loop ;
                           (ILOAD 2)    ;  13  [end:] ;
                           (HALT))))    ;  14  ``return'' a ;

        (s_f (m1 s_i 82)))              ; run s_i 82 steps ;
   (and (good-statep s_i)               ; check that both states good ;
        (good-statep s_f)
        (haltedp s_f)                   ; and that s_f is halted and ;
        (equal (top (stack s_f)) (* 7 9)))) ; the answer is correct ;
||#

; If you start ACL2 and do (include-book "m1") and (in-package "M1"), and then
; evaluate the above expression, the result is T.

; =================================================================
; Lemmas for Proving M1 Code

; In order to prove that M1 bytecode program satisfy their functional
; specifications we need some lemmas about the model.  Those lemmas
; are stated and proved below.  But I do not recommend that you read them
; now!

(defthm top-push
  (equal (top (push x y)) x))

(defthm pop-push
  (equal (pop (push x y)) y))

(defun popn (n stk)
  (if (zp n)
      stk
    (popn (- n 1) (pop stk))))

(defmacro push* (&rest lst)
  (if (endp lst)
      nil
      (if (endp (cdr lst))
          (car lst)
          `(push ,(car lst) (push* ,@(cdr lst))))))

(defthm len-push
  (equal (len (push x y))
         (+ 1 (len y))))

; Arithmetic

(include-book "arithmetic-5/top" :dir :system)

; Abstract Data Type Stuff

(defthm constant-stacks
  (and

; These next two are needed because some push expressions evaluate to
; list constants, e.g., (push 1 (push 2 nil)) becomes '(1 2) and '(1
; 2) pattern-matches with (cons x s) but not with (push x s).

       (equal (top (cons x s)) x)
       (equal (pop (cons x s)) s))
  :hints (("Goal" :in-theory (enable top pop))))


(in-theory (disable push (:executable-counterpart push) top pop))

(defthm access-make-state
  (and (equal (pc (make-state pc locals stack program)) pc)
       (equal (locals (make-state pc locals stack program)) locals)
       (equal (stack (make-state pc locals stack program)) stack)
       (equal (program (make-state pc locals stack program)) program))

  :hints (("Goal" :in-theory (enable pc locals stack program))))

(defthm constant-states
  (and

; And we add the rules to handle constant states:

       (equal (pc (cons pc x)) pc)
       (equal (locals (cons pc (cons locals x))) locals)
       (equal (stack (cons pc (cons locals (cons stack x)))) stack)
       (equal (program (cons pc (cons locals (cons stack (cons program x)))))
              program))

  :hints (("Goal" :in-theory (enable pc locals stack program))))

(defthm len-make-state
  (equal (len (make-state pc locals stack program))
         4))

(in-theory (disable make-state (:executable-counterpart make-state)))

; Step Stuff

(defthm step-opener
  (implies (consp (next-inst s))
           (equal (step s)
                  (do-inst (next-inst s) s)))

  :hints (("Goal" :in-theory (enable step))))

(in-theory (disable step))

; Clocks and Run

(defun binary-clk+ (i j)
  (+ (nfix i) (nfix j)))

(defthm clk+-associative
  (equal (binary-clk+ (binary-clk+ i j) k)
         (binary-clk+ i (binary-clk+ j k))))

(defmacro clk+ (&rest args)
  (if (endp args)
      0
      (if (endp (cdr args))
          (car args)
          `(binary-clk+ ,(car args)
                         (clk+ ,@(cdr args))))))

(defthm m1-clk+
  (equal (m1 s (clk+ i j))
         (m1 (m1 s i) j)))

(in-theory (disable binary-clk+))

(defthm m1-opener
  (and (equal (m1 s 0) s)
       (implies (natp i)
                (equal (m1 s (+ 1 i))
                       (m1 (step s) i)))))

(in-theory (disable m1))

; Nth and update-nth

(defthm nth-add1!
  (implies (natp n)
           (equal (nth (+ 1 n) list)
                  (nth n (cdr list)))))

; Rather than rely on the more powerful built-in rule:
; (DEFTHM NTH-UPDATE-NTH
;   (EQUAL (NTH M (UPDATE-NTH N VAL L))
;          (IF (EQUAL (NFIX M) (NFIX N))
;              VAL (NTH M L)))
;   :HINTS (("Goal" :IN-THEORY (ENABLE NTH))))

; We will rely on:

(defthm nth-update-nth-natp-case
  (implies (and (natp i) (natp j))
           (equal (nth i (update-nth j v list))
                  (if (equal i j)
                      v
                    (nth i list)))))

(defthm update-nth-update-nth-1
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (update-nth i v (update-nth j w list))
                  (update-nth j w (update-nth i v list))))
  :rule-classes ((:rewrite :loop-stopper ((i j update-nth)))))

(defthm update-nth-update-nth-2
  (equal (update-nth i v (update-nth i w list))
         (update-nth i v list)))

; Len and the Locals

; In our code proofs we need this theorem to prove that certain initial states
; satisfy the good-statep predicate.

(defthm equal-len-0
  (equal (equal (len x) 0)
         (not (consp x))))
