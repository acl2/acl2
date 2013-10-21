#||

Correctness of Fact
J Strother Moore

[It is silly to put a date on this file, but it was prepared in December, 2012.
But files just like this have been prepared and verified by our provers dating
back to the late 1970s.]

This book is like fact.lisp but is formatted for a demo.  It illustrates the M1
model, informally relates it to the JVM, shows that we can execute it on
concrete data, and shows how we prove theorems about its programs.

M1 is an idealized machine loosely based on the Java Virtual Machine.  It
supports only a few of the JVM's instructions but provides true (unbounded)
integer arithmetic and so is strictly more powerful.

Suppose the Demo.java contains:

class Demo {
  public static int fact(int n){
      int a = 1;
      while (n!=0) {a = n*a; n = n-1;}
      return a;
  }

  public static void main(String[] args){
      int n = Integer.parseInt(args[0], 10);
      System.out.println(fact(n));
      return;
    }
}

Suppose you compile it with:

 % javac Demo.java

and then use

 % javap -c Demo

to print the class file.  Inspecting the JVM bytecode for fact you will see:

public static int fact(int);
  Code:
   0:	iconst_1
   1:	istore_1
   2:	iload_0
   3:	ifeq	17   // see note 1 below
   6:	iload_0
   7:	iload_1
   8:	imul
   9:	istore_1
   10:	iload_0
   11:	iconst_1
   12:	isub
   13:	istore_0
   14:	goto	2   // see note 1 below
   17:	iload_1
   18:	ireturn     // see note 2 below

Note 1: The actual JVM bytecode for the ifeq and goto instructions contains the
OFFSETS from the current program counter to the target program counter, but the
javap utility prints the absolute target.

Note 2: The actual JVM bytecode for fact terminates with an ireturn to return a
32-bit int to its caller.  M1 does not support method invocation and our code,
below, simply halts with the answer on the stack.

In this file we show how M1 models this and how we can prove a theorem stating
its total correctness: that the program always terminates and computes the
mathematical factorial of its natural number input.

This file assumes you have verified the book m1.lisp on this directory.  To use
this file, start ACL2 and execute each of the commands below.  Some commands
just show how certain functions in the model are defined, other commands define
new functions or constants, other commands just run the functions to illustrate
their behavior, and still other commands prove theorems.

||#

; Start your acl2:
; % acl2 (or whatever command you use)

; Include the book:
(include-book "m1")

; Declare all symbols to be in the M1 package by default.
(in-package "M1")

; Here are the definitions of the M1 model, from the top-level
; interpreter, M1, down:

(pe 'm1)
(pe 'step)
(pe 'next-inst)
(pe 'do-inst)

; Inspection of do-inst will reveal that if the current instruction is not one
; of those named, the next state is identical to the current state.  This means
; that M1 will never advance past this unknown instruction.  We thus adopt a
; canonical unknown instruction to halt the machine and call it HALT.  In fact,
; there are an infinite number of ``halt'' instructions -- every opcode other
; than those explicitly listed by do-inst.

; Here are the definitions of certain bytecode instructions:

(pe 'execute-ILOAD)
(pe 'make-state)
(pe 'execute-ICONST)
(pe 'execute-IADD)
(pe 'execute-ISTORE)
(pe 'execute-GOTO)
(pe 'execute-IFEQ)

; Here is an M1 ``bytecode'' program that models the JVM class file
; for fact above:

(defconst *pi*
; N and A allocated in locals 0 and 1, respectively
       '((ICONST 1) ;  0
         (ISTORE 1) ;  1     A := 1;
         (ILOAD 0)  ;  2 loop:
         (IFEQ 10)  ;  3     if N=0, goto end;
         (ILOAD 1)  ;  4
         (ILOAD 0)  ;  5
         (IMUL)     ;  6
         (ISTORE 1) ;  7     A := A*N;
         (ILOAD 0)  ;  8
         (ICONST 1) ;  9
         (ISUB)     ; 10
         (ISTORE 0) ; 11     N := N-1;
         (GOTO -10) ; 12     goto loop
         (ILOAD 1)  ; 13 end:
         (HALT))    ; 14     ``return'' A;
  )

; This demonstrates running the program on input n=5 (and a=0).
; This demonstration takes 1000 steps but it actually takes fewer
; steps to reach the HALT.

(m1 (make-state 0 '(5 0) nil *pi*) 1000)

; Note that the final stack contains 120 (which we know is 5!) and that the
; final program counter is 14, which points to the HALT instruction.

; The next two functions define exactly how many steps it takes M1 to execute
; the program on input n.  If stepped as many times as given by (clk n), M1
; arrives at the HALT instruction.

(defun loop-clk (n)
       (if (zp n)
           3
           (clk+ 11
                 (loop-clk (- n 1)))))

(defun clk (n)
       (clk+ 2 (loop-clk n)))

; This shows the same run shown previously, but now instead of taking 1000
; steps, we take exactly enough steps, (clk 5).

(m1 (make-state 0 '(5 0) nil *pi*) (clk 5))

; Observe that we reached the HALT (pc 14) with 120 on top of the stack.

; How many steps did we need?

(clk 5)

; Here is the mathematical definition of factorial:

(defun ! (n)
       (if (zp n)
           1
           (* n (! (- n 1)))))

; Here we show 5! = 120.

(! 5)

; Now we exercise the machine on a harder computation.  We use M1 to
; compute 100!

(m1 (make-state 0 '(100 0) nil *pi*) (clk 100))

(clk 100)

(! 100)

; Note that M1's answer agrees with the actual mathematical answer.

; And here we use M1 to compute 1000!

(m1 (make-state 0 '(1000 0) nil *pi*) (clk 1000))

(! 1000)

; Careful inspection will reveal that the answer is correct.

; These example executions show that M1, while a ``toy,'' is capable of some
; significant computations and that the models runs reasonably fast.

; Now we prove that this M1 program always halts with the right answer.

; First we define the algorithm that the program uses:

(defun fact1 (n a)
       (if (zp n)
           a
           (fact1 (- n 1) (* n a))))

; The broad outline of our proof will be (a) prove that the code implements the
; algorithm, and then (b) prove that the algorithm satisfies the spec.  In this
; case the code is the bytecode in *pi*, the algorithm is fact1, and the spec
; is factorial, !.

; Step (a)  - prove that the code implements the algorithm.

; We start by proving that the loop implements the algorithm and then we prove
; that if we enter the loop with a = 1 we get (fact1 n 1).

; Here we prove that the loop, when entered with arbitrary naturals n and a,
; computes the same thing as the algorithm, in loop-clk time.  Note that the
; starting pc is 2 and the starting locals are n and a.  The ending pc is 14
; (the HALT) and the ending stack has (fact1 n a) on top.

(defthm loop-is-fact1
        (implies (and (natp n)
                      (natp a))
                 (equal (m1 (make-state 2
                                        (list n a)
                                        nil
                                        *pi*)
                            (loop-clk n))
                        (make-state 14
                                    (list 0 (fact1 n a))
                                    (push (fact1 n a) nil)
                                    *pi*))))

; Now we disable loop-clk so the theorem prover does not expand it.  If the
; system cannot expand loop-clk then it will not rewrite (m1 ... (loop-clk n))
; except by applying the above theorem, loop-is-fact1.  So by disabling the
; clock function, we tell the theorem prover that it knows everything we think
; it needs to reason about that portion of the code.

(in-theory (disable loop-clk))

; Now we prove that if the program is entered from the top (pc = 0) we reach
; the HALT with the final answer (fact1 n 1).

(defthm program-is-fact1
        (implies (natp n)
                 (equal (m1 (make-state 0
                                        (list n)
                                        nil
                                        *pi*)
                            (clk n))
                        (make-state 14
                                    (list 0 (fact1 n 1))
                                    (push (fact1 n 1) nil)
                                    *pi*))))

; Now we disable the clk function for the program, again signalling that the
; only way to reason about (m1 ... (clk n)) is to use the above lemma.

(in-theory (disable clk))

; This completes Step (a). 

; Step (b) Prove that the algorithm satisfies the spec.

; In this case, we prove the general relation between the algorithm and
; factorial:

(defthm fact1-is-!
        (implies (and (natp n)
                      (natp a))
                 (equal (fact1 n a)
                        (* a (! n)))))

; Now the theorem prover can put steps (a) and (b) together to get that the
; code satisfies the spec: when entered at pc = 0 with n, it reaches the HALT
; with (! n) on the stack, in (clk n) steps.

(defthm program-correct
        (implies (natp n)
                 (equal (m1 (make-state 0
                                        (list n)
                                        nil
                                        *pi*)
                            (clk n))
                        (make-state 14
                                    (list 0 (! n))
                                    (push (! n)
                                          nil)
                                    *pi*))))

; It is sometimes desirable to omit some of the details when we ``advertize'' a
; theorem.  The result below, a simple corollary of that above, says that if
; you have an arbitrary natural number n and if you let sf be the state
; obtained by running the program from pc = 0 on n for (clk n) steps, then you
; reach the HALT and (! n) is on top of the stack.

(defthm total-correctness
        (implies (and (natp n)
                      (equal sf (m1 (make-state 0
                                                (list n)
                                                nil
                                                *pi*)
                                    (clk n))))
                 (and (haltedp sf)
                      (equal (top (stack sf))
                             (! n))))
        :rule-classes nil)
