;; -------------------------------------------------------------------------------
;;
;; Simple LLVM model for use with Codewalker
;;
;; Based on M1 model written by J Moore
;;
;; Modifications for LLVM by David S. Hardin
;;
;; DSH comments indicated by two leading semicolons
;;
;;
;  m1-version-3.lisp Copyright (C) 2014, ForrestHunt, Inc.
; 
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

#||
Simple LLVM interpreter model for use in codewalker experiments

I totally ignore the guard question.

(defpkg "LL2"
  (set-difference-eq (union-eq *acl2-exports*
                               *common-lisp-symbols-from-main-lisp-package*)
                     '(push pop pc program step
                            ; nth update-nth nth-update-nth  ; <--- stobjs use built-ins
                            )))
(certify-book "LL2" 1)
||#

(in-package "LL2")

; -----------------------------------------------------------------
; Stack Manipulation

(defun push (x y)
  (cons x y))

(defun top (stack)
  (car stack))

(defun pop (stack)
  (cdr stack))

; -----------------------------------------------------------------
; State Manipulation:

(set-verify-guards-eagerness 0)

; I name the components with the prefix "ugly-" because I don't want
; to see them in proofs!  I'm going to define a more uniform interface. 

(defstobj s ugly-pc ugly-locals ugly-memory ugly-stack ugly-program :inline t)

; Basic read/write operations on state: for each field f of a stobj, defstobj
; provides two functions, f and update-f, for accessing and updating the field
; value.  Now think about how messy it is to normalize a random mix of update
; expressions, e.g., (update-h a (update-g b (update-h c (update-f d st)))).
; So I define a pair of read/write functions that can hit each field of the
; stobj, then I prove the normalization rules, then I disable these basic
; functions.  Finally, I use the basic functions to define the field-specific
; update-f versions.  I define how to write to the cd field even though it is
; never needed.  I did this to provide a uniform interface: to access or change
; a field, use rd or wr.

(defun wr (key v s)
  (declare (xargs :stobjs (s)))
  (case key
    (:pc (update-ugly-pc v s))
    (:locals (update-ugly-locals v s))
    (:memory (update-ugly-memory v s))
    (:stack (update-ugly-stack v s))
    (:program (update-ugly-program v s))
    (otherwise s)))

(defun rd (key s)
  (declare (xargs :stobjs (s)))
  (case key
    (:pc (ugly-pc s))
    (:locals (ugly-locals s))
    (:memory (ugly-memory s))
    (:stack (ugly-stack s))
    (:program (ugly-program s))
    (otherwise 0)))

(defthm sp-wr
  (implies (sp s)
           (sp (wr loc val s))))

(in-theory (disable sp))

(defun keyp (k) (member k '(:pc :locals :memory :stack :program)))

(defthm rd-wr
  (equal (rd key1 (wr key2 v s))
         (if (and (equal key1 key2)
                  (keyp key1))
             v
             (rd key1 s))))

(defthm update-nth-update-nth-diff
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (update-nth i v (update-nth j w list))
                  (update-nth j w (update-nth i v list))))
  :rule-classes ((:rewrite :loop-stopper ((i j update-nth)))))

(defthm update-nth-update-nth-same
  (equal (update-nth i v (update-nth i w list))
         (update-nth i v list)))

(defthm update-nth-redundant
  (implies (and (natp i)
                (< i (len x))
                (equal (nth i x) v))
           (equal (update-nth i v x) x)))

(defthm wr-wr-diff
  (implies (and (keyp key1)
                (keyp key2)
                (not (equal key1 key2)))
           (equal (wr key1 v1 (wr key2 v2 s))
                  (wr key2 v2 (wr key1 v1 s))))
  :hints (("Goal" :in-theory (disable nth update-nth)))
  :rule-classes ((:rewrite :loop-stopper ((key1 key2 wr)))))
  
(defthm wr-wr-same
  (implies (keyp key1)
           (equal (wr key1 v1 (wr key1 v2 s))
                  (wr key1 v1 s))))

(defthm wr-redundant
  (implies (and (sp s)                     ; <---- added and deleted below!
                (equal (rd key s) v)
;               (equal (len s) 4)          ; <----
                )
           (equal (wr key v s) s))
  :hints (("Goal" :in-theory (enable sp))))  ; <---

;(defthm len-wr
;  (implies (equal (len s) 4)
;           (equal (len (wr key v s)) 4)))

(in-theory (disable rd wr))

; The following functions are just handy abbreviations to use in the semantics
; of the instructions.  I expect them always to be expanded into rd/wr terms.
; They could be macros.

(defun pc (s)
  (declare (xargs :stobjs (s)))
  (rd :pc s))

(defun !pc (v s)
  (declare (xargs :stobjs (s)))
  (wr :pc v s))

; There is no need to define lo and !lo since we always change indexed
; positions, not the whole field.

(defun loi (i s)
  (declare (xargs :stobjs (s)))
  (nth i (rd :locals s)))

(defun !loi (i v s)
  (declare (xargs :stobjs (s)))
  (wr :locals (update-nth i v (rd :locals s)) s))

; There is no need to define mem and !mem since we always change indexed
; positions, not the whole field.

(defun memi (i s)
  (declare (xargs :stobjs (s)))
  (nth i (rd :memory s)))

(defun !memi (i v s)
  (declare (xargs :stobjs (s)))
  (wr :memory (update-nth i v (rd :memory s)) s))

(defun stack (s)
  (declare (xargs :stobjs (s)))
  (rd :stack s))

(defun !stack (v s)
  (declare (xargs :stobjs (s)))
  (wr :stack v s))

; There is no need to define !program.

(defun program (s)
  (declare (xargs :stobjs (s)))
  (rd :program s))

(defun next-inst (s)
  (declare (xargs :stobjs (s)))
  (nth (pc s) (program s)))


; -----------------------------------------------------------------
; Instruction Accessors

(defun op-code (inst)
  (nth 0 inst))

(defun arg1 (inst)
  (nth 1 inst))

(defun arg2 (inst)
  (nth 2 inst))

(defun arg3 (inst)
  (nth 3 inst))

;; -----------------------------------------------------------------

;; The LL2 Machine

; Now we define the semantics of each instruction.  These functions are called
; ``semantic functions.''

;; Most of these functions are slight abstractions of actual LLVM instructions, 
;; and have the standard LLVM three-address form.  I have also held over a few
;; M1 stack-based instructions to be used in register initialization,
;; phi processing, etc.

; Each opcode is given semantics with an ACL2 function that takes an
; instruction (with the given opcode) and a state and returns the state
; produced by executing that instruction.  For example, the LOAD instruction,
; which looks like (LOAD j k), where j is the index of the local variable
; to be loaded, and k is the index of the local variable to be loaded from,
; is given semantics by the function execute-LOAD.  Execute-LOAD is
; the ``semantic function'' for LOAD.

; Our expectation when (execute-LOAD inst s) is called is that s is a ``good''
; state, that inst is the next instruction in s, and that inst is an LOAD
; instruction.  If all that is true, we can run execute-LOAD without error,
; i.e., without worrying whether the instruction is well-formed, whether the
; local variable of that index exists, whether incrementing the pc pushes it
; outside the bounds of the program, etc.  Because we have analogous
; expectations on the semantic function for each opcode, we wrap up these
; expectations into a single predicate.


;; Memory Instructions

;; Semantics of (GETELPTR i j k): increment the pc, and set the value of reg i to 
;; the mem address of the kth element of the structure whose base mem address is 
;; stored in the jth reg.

;; In this simple data model, all we have are arrays whose elements are of size 1,
;; so GETELPTR is just an add.

(defun execute-GETELPTR (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst) (+ (loi (arg2 inst) s) (loi (arg3 inst) s)) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (LOAD j k): increment the pc and assign the local j the value at 
;; memory address stored in local k.  Aside: We will know, by guard
;; verification, that the new pc is legal and that the value pushed is 
;; an integer.

(defun execute-LOAD (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst) (memi (loi (arg2 inst) s) s) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (STORE j k): increment the pc, and store the value stored in local
;; variable k at the memory address stored in register j.

(defun execute-STORE (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!memi (loi (arg1 inst) s) (loi (arg2 inst) s) s))
         (s (!pc (+ 1 (pc s)) s)))
      s))


;; Arithmetic/Logic Instructions

;; Semantics of (ADD a b c): increment the pc, and set the value of the first reg  
;; to the sum of the second and third regs.

(defun execute-ADD (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst) (+ (loi (arg2 inst) s) (loi (arg3 inst) s)) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (EQ a b c): increment the pc, and set the value of the first reg
;; as follows: if the second reg is equal to the third reg, set the first reg to 1
;; if the second reg is not equal to the third reg, set the first reg to 0.

(defun execute-EQ (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst)
                  (if (= (loi (arg2 inst) s) (loi (arg3 inst) s)) 1 0) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (GE a b c): increment the pc, and set the value of the first reg
;; as follows: if the second reg is greater than or equal to the third reg, set  
;; the first reg to 1. If the second reg is less than the third reg, set the
;; first reg to 0.

(defun execute-GE (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst)
                  (if (>= (loi (arg2 inst) s) (loi (arg3 inst) s)) 1 0) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (GT a b c): increment the pc, and set the value of the first reg
;; as follows: if the second reg is greater than the third reg, set the first reg 
;; to 1.  If the second reg is less than or equal to the third reg, set the first
;; reg to 0.

(defun execute-GT (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst)
                  (if (> (loi (arg2 inst) s) (loi (arg3 inst) s)) 1 0) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (LE a b c): increment the pc, and set the value of the first reg
;; as follows: if the second reg is less than or equal to the third reg, set the
;; first reg to 1. If the second reg is greater than the third reg, set the first
;; reg to 0.

(defun execute-LE (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst)
                  (if (<= (loi (arg2 inst) s) (loi (arg3 inst) s)) 1 0) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (LT a b c): increment the pc, and set the value of the first reg
;; as follows: if the second reg is less than the third reg, set the first reg
;; to 1 if the second reg is greater than or equal to the third reg, set the
;; first reg to 0.

(defun execute-LT (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst)
                  (if (< (loi (arg2 inst) s) (loi (arg3 inst) s)) 1 0) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (MUL a b c): increment the pc, and set the value of the first reg 
;; to the product of the second and third regs.

(defun execute-MUL (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst) (* (loi (arg2 inst) s) (loi (arg3 inst) s)) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (SUB a b c): increment the pc, and set the value of the first reg
;; to the difference of the second and third regs.

(defun execute-SUB (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!loi (arg1 inst) (- (loi (arg2 inst) s) (loi (arg3 inst) s)) s))
         (s (!pc (+ 1 (pc s)) s)))
    s))


;; Transfer of Control Instructions

;; Semantics of (BR i j k): increment the pc by j if the first reg is non-zero
;; and by k if it is 0.  Aside: We will know, by guard verification, that the
;; new pc is legal.

(defun execute-BR (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!pc (if (not (= (loi (arg1 inst) s) 0))
                     (+ (arg2 inst) (pc s))
                   (+ (arg3 inst) (pc s)))
                   s)))
      s))

;; Semantics of (GOTO k): increment the pc by k.  Aside: We will know, by guard
;; verification, that the new pc is legal.

(defun execute-GOTO (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!pc (+ (arg1 inst) (pc s)) s)))
    s))

;; Semantics of (NOP): increment the pc.

(defun execute-NOP (inst s)
  (declare (xargs :stobjs (s))
           (ignore inst))
  (let* ((s (!pc (+ 1 (pc s)) s)))
    s))


;; Stack instructions

;; Semantics of (CONST k): increment the pc and push k onto the stack.

(defun execute-CONST (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!stack (push (arg1 inst) (stack s))
                    s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (POP): increment the pc and pop the stack.

(defun execute-POP (inst s)
  (declare (xargs :stobjs (s))
           (ignore inst))
  (let* ((s (!stack (pop (stack s))
                    s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

;; Semantics of (POPTO k): increment the pc, pop one item off the stack, and
;; store it as the value of local variable k.

(defun execute-POPTO (inst s)
  (declare (xargs :stobjs (s)))
  (let ((u (top (stack s)))
        (stack1 (pop (stack s))))
    (let* ((s (!stack stack1 s))
           (s (!loi (arg1 inst) u s))
           (s (!pc (+ 1 (pc s)) s)))
      s)))

;; Semantics of (PUSH k): increment the pc and push onto the stack the value of
;; the kth local.  Aside: We will know, by guard verification, that the new pc
;; is legal and that the value pushed is an integer.

(defun execute-PUSH (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!stack (push (loi (arg1 inst) s) (stack s))
                    s))
         (s (!pc (+ 1 (pc s)) s)))
    s))


;; Instruction selector

(defun do-inst (inst s)
  (declare (xargs :stobjs (s)))
  (if (equal (op-code inst) 'ADD)
      (execute-ADD inst s)
    (if (equal (op-code inst) 'BR)
        (execute-BR inst s)
      (if (equal (op-code inst) 'CONST)
          (execute-CONST inst s)
        (if (equal (op-code inst) 'EQ)
            (execute-EQ inst s)
          (if (equal (op-code inst) 'GE)
              (execute-GE inst s)
            (if (equal (op-code inst) 'GETELPTR)
                (execute-GETELPTR inst s)
              (if (equal (op-code inst) 'GOTO)
                  (execute-GOTO inst s)
                (if (equal (op-code inst) 'GT)
                    (execute-GT inst s)
                  (if (equal (op-code inst) 'LE)
                      (execute-LE inst s)
                    (if (equal (op-code inst) 'LOAD)
                        (execute-LOAD inst s)
                      (if (equal (op-code inst) 'LT)
                          (execute-LT inst s)
                        (if (equal (op-code inst) 'MUL)
                            (execute-MUL inst s)
                          (if (equal (op-code inst) 'NOP)
                              (execute-NOP inst s)
                            (if (equal (op-code inst) 'POP)
                                (execute-POP inst s)
                              (if (equal (op-code inst) 'POPTO)
                                  (execute-POPTO inst s)
                                (if (equal (op-code inst) 'PUSH)
                                    (execute-PUSH inst s)
                                  (if (equal (op-code inst) 'STORE)
                                      (execute-STORE inst s)
                                    (if (equal (op-code inst) 'SUB)
                                        (execute-SUB inst s)
                                      s)))))))))))))))))))

; This is the single-step function: it executes the next instruction in a
; state.  Aside: We will know, by guard verification, that the resulting state
; is a good state.

(defun step (s)
  (declare (xargs :stobjs (s)))
    (let ((s (do-inst (next-inst s) s)))
      s))

(defun haltedp (s)
  (declare (xargs :stobjs (s)))
  (equal (next-inst s) '(HALT)))


;; The top-level machine interpreter

(defun ll2 (s n)
  (declare (xargs :stobjs (s)))
  (if (zp n)
      s
      (let* ((s (step s)))
        (ll2 s (- n 1)))))


;; =================================================================
;; Lemmas for Proving LL2 Code

;; Arithmetic

(include-book "arithmetic-5/top" :dir :system)

; Stacks

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

; Step Stuff

(defthm step-opener
  (implies (and (consp (next-inst s)))
           (equal (step s)
                  (do-inst (next-inst s) s)))
  :hints (("Goal" :in-theory (enable step))))


(in-theory (disable step))

; Schedules and Run

(defun binary-clk+ (i j)
  (+ (nfix i) (nfix j)))

(defthm clk+-associative
  (equal (binary-clk+ (binary-clk+ i j) k)
         (binary-clk+ i (binary-clk+ j k))))

(defmacro clk+ (&rest argst)
  (if (endp argst)
      0
      (if (endp (cdr argst))
          (car argst)
          `(binary-clk+ ,(car argst)
                         (clk+ ,@(cdr argst))))))

(defthm ll2-clk+
  (equal (ll2 s (clk+ i j))
         (ll2 (ll2 s i) j)))

(in-theory (disable binary-clk+))

(defthm ll2-opener
  (and (equal (ll2 s 0) s)
       (implies (natp i)
                (equal (ll2 s (+ 1 i))
                       (ll2 (step s) i)))))

(in-theory (disable ll2))

; Nth and update-nth


; Len and the Locals

; In our code proofs we need this theorem to prove that certain initial states
; satisfy the good-statep predicate.

(defthm equal-len-0
  (equal (equal (len x) 0)
         (not (consp x))))
