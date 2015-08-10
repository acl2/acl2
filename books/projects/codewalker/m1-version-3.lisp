; Copyright (C) 2014, ForrestHunt, Inc.
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

#||
Like m1-version-1 but uses stobjs.

I totally ignore the guard question.

See the README file on this directory for an overview of this work.

(defpkg "M1"
  (set-difference-eq (union-eq *acl2-exports*
                               *common-lisp-symbols-from-main-lisp-package*)
                     '(push pop pc program step
                            ; nth update-nth nth-update-nth  ; <--- stobjs use built-ins
                            )))
(certify-book "m1-version-3" 1)
||#

(in-package "M1")

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

(defstobj s ugly-pc ugly-locals ugly-stack ugly-program)

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
    (:stack (update-ugly-stack v s))
    (:program (update-ugly-program v s))
    (otherwise s)))

(defun rd (key s)
  (declare (xargs :stobjs (s)))
  (case key
    (:pc (ugly-pc s))
    (:locals (ugly-locals s))
    (:stack (ugly-stack s))
    (:program (ugly-program s))
    (otherwise 0)))

(defthm sp-wr
  (implies (sp s)
           (sp (wr loc val s))))

(in-theory (disable sp))

(defun keyp (k) (member k '(:pc :locals :stack :program)))

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

; -----------------------------------------------------------------

; The M1 Machine

; Now we define the semantics of each instruction.  These functions are called
; ``semantic functions.''

; Each opcode will be given semantics with an ACL2 function that takes an
; instruction (with the given opcode) and a state and returns the state
; produced by executing the instruction.  For example, the ILOAD instruction,
; which looks like this (ILOAD k), where k is the index of the local variable
; to be loaded, is given semantics by the function execute-ILOAD.  Execute-ILOAD is
; the ``semantic function'' for ILOAD.

; Our expectation when (execute-ILOAD inst s) is called is that s is a ``good''
; M1 state, that inst is the next instruction in s, and that inst is an ILOAD
; instruction.  If all that is true, we can run execute-ILOAD without error,
; i.e., without worrying whether the instruction is well-formed, whether the
; local variable of that index exists, whether incrementing the pc pushes it
; outside the bounds of the program, etc.  Because we have analogous
; expectations on the semantic function for each opcode, we wrap up these
; expectations into a single predicate:

; Semantics of (ILOAD k): increment the pc and push onto the stack the value of
; the kth local.  Aside: We will know, by guard verification, that the new pc
; is legal and that the value pushed is a rational number.  As a rule, I will
; not comment here on everything we know by guard verification, I'm just trying
; to give you a sense of the implications of our expectations.

(defun execute-ILOAD (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!stack (push (loi (arg1 inst) s) (stack s))
                    s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

; Semantics of (ICONST k):  increment the pc and push k onto the stack.

(defun execute-ICONST (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!stack (push (arg1 inst) (stack s))
                    s))
         (s (!pc (+ 1 (pc s)) s)))
    s))

; Semantics of (IADD): increment the pc, pop two items off the stack and push
; their sum.  Aside: We will know, by guard verification, that there are at
; least two items on the stack and that they are both rational numbers.

(defun execute-IADD (inst s)
  (declare (xargs :stobjs (s))
           (ignore inst))
  (let ((u (top (stack s)))
        (v (top (pop (stack s))))
        (stack1 (pop (pop (stack s)))))
    (let* ((s (!stack (push (+ v u) stack1) s))
           (s (!pc (+ 1 (pc s)) s)))
      s)))

; Semantics of (ISUB): increment the pc, pop two items off the stack and push
; their difference.

(defun execute-ISUB (inst s)
  (declare (xargs :stobjs (s))
           (ignore inst))
  (let ((u (top (stack s)))
        (v (top (pop (stack s))))
        (stack1 (pop (pop (stack s)))))
    (let* ((s (!stack (push (- v u) stack1) s))
           (s (!pc (+ 1 (pc s)) s)))
      s)))

; Semantics of (IMUL): increment the ic, pop two items off the stack and push
; their product.

(defun execute-IMUL (inst s)
  (declare (xargs :stobjs (s))
           (ignore inst))
  (let ((u (top (stack s)))
        (v (top (pop (stack s))))
        (stack1 (pop (pop (stack s)))))
    (let* ((s (!stack (push (* v u) stack1) s))
           (s (!pc (+ 1 (pc s)) s)))
      s)))

; Semantics of (ISTORE k): increment the ic, pop one item off the stack, and
; store it as the value of local variable k.

(defun execute-ISTORE (inst s)
  (declare (xargs :stobjs (s)))
  (let ((u (top (stack s)))
        (stack1 (pop (stack s))))
    (let* ((s (!stack stack1 s))
           (s (!loi (arg1 inst) u s))
           (s (!pc (+ 1 (pc s)) s)))
      s)))

; Semantics of (GOTO k): increment the pc by k.  Aside: We will know, by guard
; verification, that the new pc is legal.

(defun execute-GOTO (inst s)
  (declare (xargs :stobjs (s)))
  (let* ((s (!pc (+ (arg1 inst) (pc s)) s)))
    s))

; Semantics of (IFEQ k): pop one item off the stack and increment the pc k if
; that item is 0 and by 1 if if is non-0.  Aside: We will know, by guard
; verification, that the new pc is legal.

(defun execute-IFEQ (inst s)
  (declare (xargs :stobjs (s)))
  (let ((u (top (stack s)))
        (stack1 (pop (stack s))))
    (let* ((s (!stack stack1 s))
           (s (!pc (if (equal u 0)
                       (+ (arg1 inst) (pc s))
                       (+ 1 (pc s)))
                   s)))
      s)))

(defun do-inst (inst s)
  (declare (xargs :stobjs (s)))
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
  (declare (xargs :stobjs (s)))
  (do-inst (next-inst s) s))

(defun m1 (s n)
  (declare (xargs :stobjs (s)))
  (if (zp n)
      s
      (let* ((s (step s)))
        (m1 s (- n 1)))))

(defun haltedp (s)
  (declare (xargs :stobjs (s)))
  (equal (next-inst s) '(HALT)))

; =================================================================
; Lemmas for Proving M1 Code

; Arithmetic

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
  (implies (consp (next-inst s))
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




; Len and the Locals

; In our code proofs we need this theorem to prove that certain initial states
; satisfy the good-statep predicate.

(defthm equal-len-0
  (equal (equal (len x) 0)
         (not (consp x))))
