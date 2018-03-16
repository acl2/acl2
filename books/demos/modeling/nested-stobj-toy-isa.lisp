; Matt Kaufmann
; Copyright (C) 2013, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book illustrates the use of stobjs with stobj fields for modeling an
; instruction set architectures (ISA).  Also see :DOC stobj-let and for further
; examples employing stobjs with stobj fields, see ACL2 community book
; demos/modeling/nested-stobj-toy-isa.lisp.

; We work a little example based on a query from Sandip Ray.  It is a model of
; a toy multiprocessor with shared memory.  This is perhaps too trivial even to
; call a toy!  But it illustrates the idea of structuring the state.

(in-package "ACL2")

; First, introduce the uniprocessor state.

; Note that we keep all the new rules disabled.  That may not be necessary, but
; it seems a reasonable way to start, to avoid explosions during proofs caused
; by opening up all function symbols.  In fact, throughout this file we tightly
; control what is enabled.  (In an early attempt we didn't try to do that, and
; proofs seemed to explode and thus to be difficult to control.)

(deflabel pre-uni-state)
(defstobj uni-state
  (instructions :type (array (unsigned-byte 8) (1024))
                :initially 0)
  (iptr :type (integer 0 1023)
        :initially 0)
  stack)
(in-theory (current-theory 'pre-uni-state))

; Our toy model has 16-bit data and a 16-bit address space.

(defconst *2^16* (expt 2 16))

; Next, introduce the shared state.  We include in that state not only the
; memory, but also an index for the "current" uniprocessor, as we will use
; round-robin scheduling for multiprocessor execution.

(deflabel pre-shared-state)
(defstobj shared-state
  (shared-memory :type (array (unsigned-byte 16) (*2^16*))
                 :initially 0)
  (uni-index :type (integer 0 3)
             :initially 0))
(in-theory (current-theory 'pre-shared-state))

; For us, a multiprocessor state is an array of 4 uniprocessor states together
; with a shared state.

(deflabel pre-multi-state)
(defstobj multi-state
  (uni :type (array uni-state (4))) ; 4 processors
  (shared :type shared-state))
(in-theory (current-theory 'pre-multi-state))

; Next, it is convenient to introduce a function that pulls a 16-bit number off
; the stack, returning 0 if the top of the stack fails to be a 16-bit number.

(defun top-word (x)
  (declare (xargs :guard t))
  (let ((addr (and (consp x)
                   (car x))))
    (if (and (natp addr)
             (< addr *2^16*))
        addr
      0)))

(defthm top-word-is-word
  (and (natp (top-word x))
       (< (top-word x) *2^16*))
  :rule-classes ((:type-prescription
                  :corollary (natp (top-word x)))
                 (:rewrite
                  :corollary (< (top-word x) *2^16*))))

(in-theory (disable top-word))

; Our next goal is to define uni-step, a function that steps a uniprocessor
; state.

; It is convenient to introduce a function for popping the stack, without
; concern for whether the stack is a nil-terminated list.

(defund popped-stack (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cdr x)
    nil))

; Here is our tiny machine language.

(defconst *nop* 0)
(defconst *add* 1)
(defconst *load* 2)
(defconst *store* 3)
(defconst *swap* 4)

; Next, we do a little bit of proof and theory manipulation to admit uni-step.

(defthm natp-iptr
  (implies (uni-statep uni-state)
           (natp (iptr uni-state)))
  :hints (("Goal" :in-theory (enable iptr uni-statep)))
  :rule-classes :type-prescription)

(in-theory (enable instructions-length)) ; simplest, since this is a constant

(defthm iptr-instructions-length
  (implies (uni-statep uni-state)
           (< (iptr uni-state)
              1024))
  :hints (("Goal" :in-theory (enable iptr uni-statep)))
  :rule-classes :linear)

(in-theory (enable shared-memory-length)) ; simplest, since this is a constant

(defun uni-step (uni-state shared-state)
  (declare (xargs :stobjs (uni-state shared-state)))
  (let* ((iptr (iptr uni-state))
         (inst (instructionsi iptr uni-state))
         (stack (stack uni-state))
         (new-iptr (1+ iptr))
         (uni-state (update-iptr (if (eql new-iptr 1024)
                                     0
                                   new-iptr)
                                 uni-state)))
    (cond
     ((eql inst *add*)
      (let ((uni-state (update-stack (cons (+ (top-word stack)
                                              (top-word (popped-stack stack)))
                                           (popped-stack (popped-stack stack)))
                                     uni-state)))
        (mv uni-state shared-state)))
     ((eql inst *load*)
      (let* ((val (shared-memoryi (top-word stack) shared-state))
             (uni-state
              (update-stack (cons val (popped-stack stack)) uni-state)))
        (mv uni-state shared-state)))
     ((eql inst *store*)
      (let* ((addr (top-word stack))
             (stack1 (popped-stack stack))
             (val (top-word stack1))
             (stack2 (popped-stack stack1))
             (shared-state
              (update-shared-memoryi addr val shared-state))
             (uni-state
              (update-stack stack2 uni-state)))
        (mv uni-state shared-state)))
     ((eql inst *swap*)
      (let ((uni-state
             (update-stack (cons (top-word (popped-stack stack))
                                 (cons (top-word stack)
                                       (popped-stack (popped-stack stack))))
                           uni-state)))
        (mv uni-state shared-state)))
     (t ; no-op
      (mv uni-state shared-state)))))

; Our next goal is to define a function, get-index, that gets the index of the
; next processor to step and also updates the state by updating that index.  We
; need to prove some lemmas.

; We start with uni-statep-car-uni-step, which requires sublemmas, as follows.

(defthm uni-statep-update-stack
  (implies (uni-statep uni-state)
           (uni-statep (update-stack stack uni-state)))
  :hints (("Goal" :in-theory (enable uni-statep update-stack))))

(defthm uni-statep-update-iptr
  (implies (and (uni-statep uni-state)
                (iptrp iptr))
           (uni-statep (update-iptr iptr uni-state)))
  :hints (("Goal" :in-theory (enable uni-statep update-iptr))))

(in-theory (enable iptrp)) ; simple function; seems easiest just to enable it

(defthm uni-statep-car-uni-step
  (implies (and (uni-statep uni-state)
                (shared-statep shared-state))
           (uni-statep (car (uni-step uni-state shared-state)))))

(defthm uni-index-range
  (implies (shared-statep shared-state)
           (and (natp (uni-index shared-state))
                (<= (uni-index shared-state) 3)))
  :hints (("Goal" :in-theory (enable uni-index shared-statep)))
  :rule-classes ((:type-prescription
                  :corollary (implies (shared-statep shared-state)
                                      (natp (uni-index shared-state))))
                 (:linear
                  :corollary (implies (shared-statep shared-state)
                                      (<= (uni-index shared-state) 3)))))

(defthm multi-statep-forward-to-shared-statep
  (implies (multi-statep multi-state)
           (shared-statep (shared multi-state)))
  :hints (("Goal" :in-theory (enable multi-statep sharedp shared)))
  :rule-classes :forward-chaining)

(defthm shared-statep-update-uni-index
  (implies (and (shared-statep shared-state)
                (uni-indexp index))
           (shared-statep (update-uni-index index shared-state)))
  :hints (("Goal" :in-theory (enable shared-statep update-uni-index))))

(in-theory (enable uni-indexp))

(defun get-index (multi-state)
  (declare (xargs :stobjs multi-state))
  (stobj-let ((shared-state (shared multi-state)))
             (index shared-state)
             (let* ((index (uni-index shared-state))
                    (next-index (if (eql index 3) 0 (1+ index)))
                    (shared-state (update-uni-index next-index shared-state)))
               (mv index shared-state))
             (mv index multi-state)))

; Our next goal is to introduce a function multi-step, which takes a single
; step on a multiprocessor state.

; We first do a bit of trivial theory manipulation, and then we look at
; checkpoints from attempts to admit multi-step in order to construct useful
; lemmas.

(in-theory (disable uni-step))

(in-theory (enable uni-length))

(defthm shared-update-shared
  (equal (shared (update-shared shared-state multi-state))
         shared-state)
  :hints (("Goal" :in-theory (enable shared update-shared))))

(defthm unii-update-shared
  (equal (unii i1 (update-shared shared-state multi-state))
         (unii i1 multi-state))
  :hints (("Goal" :in-theory (enable update-shared unii))))

(in-theory (enable uni-indexp))

(defthm uni-statep-unii-lemma
  (implies (and (unip u)
                (<= 0 index)
                (< index (len u)))
           (uni-statep (nth index u)))
  :hints (("Goal" :in-theory (enable uni-statep unip))))

(defthm uni-statep-unii
  (implies (and (multi-statep multi-state)
                (uni-indexp index))
           (uni-statep (unii index multi-state)))
  :hints (("Goal" :in-theory (enable unii multi-statep))))

; Start proof of shared-statep-mv-nth-1-uni-step.

(defthm shared-memoryp-update-shared-memoryi
  (implies (and (shared-memoryp mem)
                (natp addr)
                (< addr (len mem))
                (unsigned-byte-p 16 word))
           (shared-memoryp (update-nth addr word mem)))
  :hints (("Goal" :in-theory (enable shared-memoryp))))

(defthm shared-statep-update-shared-memoryi
  (implies (and (shared-statep shared-state)
                (natp addr)
                (< addr *2^16*)
                (unsigned-byte-p 16 word))
           (shared-statep (update-shared-memoryi addr word shared-state)))
  :hints (("Goal" :in-theory (enable shared-statep update-shared-memoryi))))

(defthm shared-statep-mv-nth-1-uni-step
  (implies (and (uni-statep uni-state)
                (shared-statep shared-state))
           (shared-statep (mv-nth 1 (uni-step uni-state shared-state))))
  :hints (("Goal" :in-theory (enable uni-step))))

; Start development of display-multi-state, a debug utility used in
; multi-step.

(defun display-shared-memory (index shared-state alist)
  (declare (xargs :stobjs shared-state
                  :guard (and (alistp alist)
                              (natp index)
                              (<= index *2^16*))))
  (cond ((zp index) alist)
        (t (let* ((index (1- index))
                  (val (shared-memoryi index shared-state)))
             (display-shared-memory index
                                    shared-state
                                    (if (eql val 0)
                                        alist
                                      (acons index val alist)))))))

(defun display-multi-state (index multi-state shared-memory-p)
  (declare (xargs :stobjs multi-state)
           (type (integer 0 3) index))
  (stobj-let
   ((shared-state (shared multi-state))
    (uni-state (unii index multi-state)))
   (val)
   (let* ((iptr (iptr uni-state))
          (instr (instructionsi iptr uni-state))
          (head (and (not (eq shared-memory-p :only))
                     `(:multi-state
                       :index ,index
                       :iptr ,iptr
                       :instruction ,(cond ((eql instr *add*) 'add)
                                           ((eql instr *load*) 'load)
                                           ((eql instr *store*) 'store)
                                           ((eql instr *swap*) 'swap)
                                           (t 'nop))
                       :stack ,(stack uni-state))))
          (tail (and shared-memory-p
                     `(:shared-memory ,(display-shared-memory
                                        *2^16* shared-state nil)))))
     (cond ((eq shared-memory-p :only)
            tail)
           ((null shared-memory-p)
            head)
           (t (append head tail))))
   val))

(defmacro print-multi-state (index multi-state &optional (shared-memory-p 't))
  `(cw "~y0" (display-multi-state ,index ,multi-state ,shared-memory-p)))

(defun multi-step (multi-state debug)
  (declare (xargs :stobjs multi-state
                  :guard (true-listp debug)))
  (mv-let (index multi-state)
          (get-index multi-state)
          (prog2$ (if (member index debug)
                      (print-multi-state index multi-state)
                    nil)
                  (stobj-let ((uni-state (unii index multi-state))
                              (shared-state (shared multi-state)))
                             (uni-state shared-state)
                             (uni-step uni-state shared-state)
                             multi-state))))

; Having defined multi-step, we define our interpreter, multi-run, to run
; multi-step for a given number of steps.  This is a standard interpreter-style
; definition.

(defun print-multi-state-all (multi-state)
  (declare (xargs :stobjs multi-state))
  (progn$ (cw "-----~%")
          (print-multi-state 0 multi-state :only)
          (print-multi-state 0 multi-state nil)
          (print-multi-state 1 multi-state nil)
          (print-multi-state 2 multi-state nil)
          (print-multi-state 3 multi-state nil)))

(defun multi-run (n multi-state debug)
  (declare (xargs :stobjs multi-state
                  :guard (and (natp n)
                              (true-listp debug))))
  (cond ((zp n)
         (prog2$ (if debug
                     (print-multi-state-all multi-state)
                   nil)
                 multi-state))
        (t (let ((multi-state (multi-step multi-state debug)))
             (multi-run (1- n) multi-state debug)))))

; Now let's do a small test of multi-run -- just enough to get a sense that we
; didn't make a major blunder.  We'll just use two processors, starting with
; suitable stacks so that we get the following behavior, which relies on our
; round-robin scheduling.  For initialization, we'll save ourselves the trouble
; of verifying guards, since not much is to be learned from that exercise and
; execution speed isn't an issue for this small test.

; P0                    P1
;   (0 100 2 120 1 3)     (1 20 3 40 2 0)
; --                    --
; st(0,100)
;   (2 120 1 3)
;                       st(1,20)
;                         (3 40 2 0)
; st(2,120)
;   (1 3)
;                       st(3,40)
;                         (2 0)
; ld(1,20)
;   (20 3)
;                       ld(2,120)
;                         (120 0)
; swap
;   (3 20)
;                       swap
;                         (0 120)
; ld(3,40)
;   (40 20)
;                       ld(0,100)
;                         (100 120)
; add
;   (60)
;                       add
;                         (220)

; We load a given list of instructions, starting at instruction index iptr,
; into a given uniprocessor state.

(defun load-instructions (iptr instrs uni-state)
  (declare (type (integer 0 1023) iptr)
           (xargs :stobjs uni-state
                  :guard (and (true-listp instrs)
                              (< (+ iptr (len instrs)) 1024))))
  (cond ((endp instrs) uni-state)
        (t (let ((uni-state
                  (update-instructionsi iptr
                                        (if (unsigned-byte-p 8 (car instrs))
                                            (car instrs)
                                          0)
                                        uni-state)))
             (load-instructions (1+ iptr) (cdr instrs) uni-state)))))

; The following constants are used to initialize the state from which we'll run
; our test.

(defconst *test-instructions-0*
  (list *store* *store* *load* *swap* *load* *add*))

(defconst *test-instructions-1*
  (list *store* *store* *load* *swap* *load* *add*))

(defconst *test-stack-0*
  '(0 100 2 120 1 3))

(defconst *test-stack-1*
  '(1 20 3 40 2 0))

; Next comes our function to initialize the index-th uniprocessor state in a
; given multiprocessor state, using the given stack and instructions.

(defun init-multi-state-uni (index stack instructions multi-state)
  (declare (xargs :stobjs multi-state
                  :verify-guards nil))
  (stobj-let
   ((uni-state (unii index multi-state)))
   (uni-state)
   (let* ((uni-state (update-stack stack uni-state))
          (uni-state (load-instructions 0 instructions uni-state))
          (uni-state (update-iptr 0 uni-state)))
     uni-state)
   multi-state))

; Our initial shared memory consists of all zeros.

(defun init-shared-memory (index shared-state)
  (declare (xargs :stobjs shared-state
                  :guard (and (natp index)
                              (<= index *2^16*))))
  (cond ((zp index) shared-state)
        (t (let* ((index (1- index))
                  (shared-state (update-shared-memoryi index 0 shared-state)))
             (init-shared-memory index shared-state)))))

; The shared component of our multiprocessor state is initialized with all
; zeros.

(defun init-multi-state-shared (multi-state)
  (declare (xargs :stobjs multi-state
                  :verify-guards nil))
  (stobj-let ((shared-state (shared multi-state)))
             (shared-state)
             (let ((shared-state (init-shared-memory *2^16* shared-state)))
               (update-uni-index 0 shared-state))
             multi-state))

; Finally, here is our function to initialize a given multiprocessor state.

(defun init-multi-state (multi-state)
  (declare (xargs :stobjs multi-state
                  :verify-guards nil))
  (let* ((multi-state (init-multi-state-uni 0
                                            *test-stack-0*
                                            *test-instructions-0*
                                            multi-state))
         (multi-state (init-multi-state-uni 1
                                            *test-stack-1*
                                            *test-instructions-1*
                                            multi-state))
         (multi-state (init-multi-state-shared multi-state)))
    multi-state))

; At this point we can run our state.  To see a trace of the execution, evaluate
; (let ((multi-state (init-multi-state multi-state)))
;      (multi-run 24 multi-state '(0 1)))
; -- or, to include the irrelevant processors as well:
; (let ((multi-state (init-multi-state multi-state)))
;      (multi-run 24 multi-state '(0 1 2 3)))

; The following function is just used by our test mechanism, below.

(defun get-stack (index multi-state)
  (declare (xargs :stobjs multi-state
                  :guard (uni-indexp index)))
  (stobj-let ((uni-state (unii index multi-state)))
             (stack)
             (stack uni-state)
             stack))

; Compilation is necessary here for Allegro CL.
; However, it causes a failure in
; CMU Common Lisp snapshot-2014-06  (20E Unicode),
; and
; CMU Common Lisp snapshot-2014-12  (20F Unicode)
; and probably other CMUCL versions -- presumably a compiler bug.
; Some day perhaps someone will investigate and then report the CMUCL bug
; using a small replayable example.
(make-event
 (if (equal (@ host-lisp) :CMU)
     (value '(value-triple nil))
   (value '(comp t))))

; And finally, here is our test.  We use top-level because with-local-stobj is
; not allowed at the top level of evaluation (during make-event expansion as
; below, or even directly in the top-level loop).

(make-event
 (er-progn (top-level
            (with-local-stobj
             multi-state
             (mv-let (result multi-state)
                     (let* ((multi-state (init-multi-state multi-state))
                            (multi-state (multi-run 24 multi-state nil)))
                       (mv (and (equal (get-stack 0 multi-state) '(60))
                                (equal (get-stack 1 multi-state) '(220))
                                (equal (get-stack 2 multi-state) nil)
                                (equal (get-stack 3 multi-state) nil))
                           multi-state))
                     (mv (not result) nil state))))
           (value '(value-triple :success)))
; Just for fun, let's check this at include-book time too:
 :check-expansion t)
