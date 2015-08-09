#|

Before certification, define the M1 package.

I don't import certain Common Lisp symbols, like PUSH and POP, because of their
definitions are incompatible with my intended definitions below.  Others of the
symbols I don't import are defined acceptably in the ACL2 package, e.g., NTH,
but I want to students to see their definitions as warm-up exercises.

(defpkg "M1"
  (set-difference-eq (union-eq *acl2-exports*
                               *common-lisp-symbols-from-main-lisp-package*)
                     '(push pop pc program step
                            nth update-nth nth-update-nth)))

(certify-book "m1" 1)

|#

(in-package "M1")

; Warm-up:  define the basic list processing functions needed to build the model.

(defun push (x y) (cons x y))
(defun top (stack) (car stack))
(defun pop (stack) (cdr stack))

(defun nth (n list)
  (if (zp n)
      (car list)
    (nth (- n 1) (cdr list))))

(defun update-nth (n v list)
  (if (zp n)
      (cons v (cdr list))
    (cons (car list)
          (update-nth (- n 1) v (cdr list)))))

(defun make-state (pc locals stack program)
     (cons pc
           (cons locals
                 (cons stack
                       (cons program
                             nil)))))

(defun pc (s) (nth 0 s))
(defun locals (s) (nth 1 s))
(defun stack (s) (nth 2 s))
(defun program (s) (nth 3 s))

(defun op-code (inst) (nth 0 inst))
(defun arg1 (inst) (nth 1 inst))
(defun arg2 (inst) (nth 2 inst))
(defun arg3 (inst) (nth 3 inst))

; The M1 Machine

(defun next-inst (s)
  (nth (pc s) (program s)))

; Now we define the semantics of each instruction.  These
; functions are called ``semantic functions.''

(defun execute-ILOAD (inst s)
  (make-state (+ 1 (pc s))
              (locals s)
              (push (nth (arg1 inst)
                         (locals s))
                    (stack s))
              (program s)))

(defun execute-ICONST (inst s)
  (make-state (+ 1 (pc s))
              (locals s)
              (push (arg1 inst) (stack s))
              (program s)))

(defun execute-IADD (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (+ (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

(defun execute-ISUB (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (- (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

(defun execute-IMUL (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (* (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

(defun execute-ISTORE (inst s)
  (make-state (+ 1 (pc s))
              (update-nth (arg1 inst) (top (stack s)) (locals s))
              (pop (stack s))
              (program s)))

(defun execute-GOTO (inst s)
  (make-state (+ (arg1 inst) (pc s))
              (locals s)
              (stack s)
              (program s)))

(defun execute-IFEQ (inst s)
  (make-state (if (equal (top (stack s)) 0)
                  (+ (arg1 inst) (pc s))
                (+ 1 (pc s)))
              (locals s)
              (pop (stack s))
              (program s)))

(defun do-inst (inst s)
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

(defun step (s)
     (do-inst (next-inst s) s))

(defun haltedp (s)
  (equal (next-inst s) '(HALT)))

(defun m1 (s n)
  (if (zp n)
      s
      (m1 (step s) (- n 1))))

; End of the Definition of M1.  Everything else is derived from the foregoing.
; It is included in this file only so that there is one book that has
; everything you need to build and play with M1.
; -----------------------------------------------------------------

; Useful Lemmas

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

; Arithmetic

(include-book "arithmetic-5/top" :dir :system)

; Abstract Data Type Stuff

(defthm stacks
  (and (equal (top (push x s)) x)
       (equal (pop (push x s)) s)

; These next two are needed because some push expressions evaluate to
; list constants, e.g., (push 1 (push 2 nil)) becomes '(1 2) and '(1
; 2) pattern-matches with (cons x s) but not with (push x s).

       (equal (top (cons x s)) x)
       (equal (pop (cons x s)) s)))

(in-theory (disable push top pop (:executable-counterpart push)))

(defthm states
  (and (equal (pc (make-state pc locals stack program)) pc)
       (equal (locals (make-state pc locals stack program)) locals)
       (equal (stack (make-state pc locals stack program)) stack)
       (equal (program (make-state pc locals stack program)) program)

; And we add the rules to handle constant states:

       (equal (pc (cons pc x)) pc)
       (equal (locals (cons pc (cons locals x))) locals)
       (equal (stack (cons pc (cons locals (cons stack x)))) stack)
       (equal (program (cons pc (cons locals (cons stack (cons program x)))))
              program)))

(in-theory (disable make-state pc locals stack program
                    (:executable-counterpart make-state)))

; Step Stuff

(defthm step-opener
  (implies (consp (next-inst s))
           (equal (step s)
                  (do-inst (next-inst s) s))))

(in-theory (disable step))

; Schedules and Run

(defun binary-clk+ (i j)
  (+ (nfix i) (nfix j)))

(defthm clk+-associative
  (equal (binary-clk+ (binary-clk+ i j) k) (binary-clk+ i (binary-clk+ j k))))

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

(defthm nth-update-nth
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

