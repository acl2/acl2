#|
The Universal Example

J Strother Moore, Jeff Golden, Hanbing Liu, and Sandip Ray

In this file, we establish that for any int-valued function f, and
any x, there exists an M5 schedule which induces computation of (f x) by a
"universal" M5 state.  The upshot is that if one is willing to accept
a bytecode specification employing non-constructive existential
quantification of the schedule component, then we have one very simple
program which computes an entire set of interesting functions.  Too
bad such a specification is not meaningful!

Here is the code array of the "universal" method:

(defconst *universal-program*
  '((iconst_0)
    (iconst_1)
    (iadd)
    (goto -2)))

Here is our specification of the "interesting set of functions":

(encapsulate (((f *) => *))

             (local
              (defun f (x)
                (declare (ignore x))
                0))

             (defthm f-is-jvm-int-valued
               (and (integerp (f x))
                    (>= (f x) (* -1 (expt 2 31)))
                    (<= (f x) (1- (expt 2 31))))))

It constrains f to be a function of one argument that returns a Java
int.

In the context of the encapsulation above, and definitions given below, we
proved:

(defthm universal-computes-f
  (equal (top
          (stack
           (top-frame 0
                      (run (universal-schedule x)
                           *universal-state*))))
         (f x)))

If you want to know the value of a particular such f at an n, you may
thus run the "universal program" according to the schedule generated
by the schedule-generator and then look at the top of thread zero's
active operand stack.

To recertify:

(include-book "utilities")

(certify-book "universal" 1)

Sun Jun 30 23:21:06 2002

|#

(in-package "M5")

(defconst *universal-state*
  '(((0 ((0 NIL NIL
            ((INVOKESTATIC "Universal" "universal" 0)
             (POP)
             (RETURN))
            JVM::UNLOCKED "Universal"))
        SCHEDULED NIL))
    ((0 ("java.lang.Class" ("<name>" . "java.lang.Object"))
        ("java.lang.Object" ("monitor" . 0)
         ("mcount" . 0)
         ("wait-set" . 0)))
     (1 ("java.lang.Class" ("<name>" . "ARRAY"))
        ("java.lang.Object" ("monitor" . 0)
         ("mcount" . 0)
         ("wait-set" . 0)))
     (2 ("java.lang.Class" ("<name>" . "java.lang.Thread"))
        ("java.lang.Object" ("monitor" . 0)
         ("mcount" . 0)
         ("wait-set" . 0)))
     (3 ("java.lang.Class" ("<name>" . "java.lang.String"))
        ("java.lang.Object" ("monitor" . 0)
         ("mcount" . 0)
         ("wait-set" . 0)))
     (4 ("java.lang.Class" ("<name>" . "java.lang.Class"))
        ("java.lang.Object" ("monitor" . 0)
         ("mcount" . 0)
         ("wait-set" . 0)))
     (5 ("java.lang.Class" ("<name>" . "Universal"))
        ("java.lang.Object" ("monitor" . 0)
         ("mcount" . 0)
         ("wait-set" . 0))))
    (("java.lang.Object" NIL ("monitor" "mcount" "wait-set")
      NIL NIL (("<init>" NIL NIL (RETURN)))
      (REF 0))
     ("ARRAY" ("java.lang.Object")
      (("<array>" . *ARRAY*))
      NIL NIL NIL (REF 1))
     ("java.lang.Thread"
      ("java.lang.Object")
      NIL NIL NIL
      (("run" NIL NIL (RETURN))
       ("start" NIL NIL NIL)
       ("stop" NIL NIL NIL)
       ("<init>" NIL NIL (ALOAD_0)
        (INVOKESPECIAL "java.lang.Object" "<init>" 0)
        (RETURN)))
      (REF 2))
     ("java.lang.String"
      ("java.lang.Object")
      ("strcontents")
      NIL NIL
      (("<init>" NIL NIL (ALOAD_0)
        (INVOKESPECIAL "java.lang.Object" "<init>" 0)
        (RETURN)))
      (REF 3))
     ("java.lang.Class" ("java.lang.Object")
      NIL NIL NIL
      (("<init>" NIL NIL (ALOAD_0)
        (INVOKESPECIAL "java.lang.Object" "<init>" 0)
        (RETURN)))
      (REF 4))
     ("Universal" ("java.lang.Object")
      NIL NIL NIL
      (("<init>" NIL NIL (ALOAD_0)
        (INVOKESPECIAL "java.lang.Object" "<init>" 0)
        (RETURN))
       ("universal" NIL NIL
        (ICONST_0)
        (ICONST_1)
        (IADD)
        (GOTO -2))
       ("main" (|JAVA.LANG.STRING[]|)
        NIL
        (INVOKESTATIC "Universal" "universal" 0)
        (POP)
        (RETURN)))
      (REF 5)))))

; Here is the code array of the method "universal":

(defconst *universal-program*
  '((ICONST_0)    ;;; 0
    (ICONST_1)    ;;; 1
    (IADD)        ;;; 2
    (GOTO -2)))   ;;; 3

; Here is our specification of the "interesting set of functions":

(encapsulate (((f *) => *))

             (local
              (defun f (x)
                (declare (ignore x))
                0))

             (defthm f-is-jvm-int-valued
               (and (integerp (f x))
                    (>= (f x) (* -1 (expt 2 31)))
                    (<= (f x) (1- (expt 2 31))))
               :rule-classes nil))

; We provided the constraint above in terms of (expt 2 31) to make it
; understandable to outsiders.  But here is the more useful version of
; the constraint.

(defthm intp-f
  (intp (f x))
  :hints (("Goal" :in-theory (enable intp)
           :use f-is-jvm-int-valued)))

; Here is the notion of being poised at the top of the loop in the
; universal program.

(defun poised-at-universal-loop (th s i)
  (and (equal (status th s) 'SCHEDULED)
       (equal (pc (top-frame th s)) 1)
       (equal (program (top-frame th s)) *universal-program*)
       (intp (top (stack (top-frame th s))))
       (integerp i)
       (<= 0 i)))

; Here is a schedule that will drive us from the top of the loop
; sufficiently to increment the top of the stack by i.

(defun universal-loop-sched (th i)
  (if (zp i)
      nil
    (append (repeat th 3)
            (universal-loop-sched th (- i 1)))))

(defun universal-loop-hint (th s i)
  (if (zp i)
      (list th s i)
    (universal-loop-hint
     th
     (modify th s
      :stack
      (push
       (int-fix (+ 1 (top (stack (top-frame th s)))))
       (pop (stack (top-frame th s)))))
     (- i 1))))

; These ought to be in utilities.lisp

(defthm universal-loop-behavior
  (implies (poised-at-universal-loop th s i)
           (equal (run (universal-loop-sched th i) s)
                  (if (zp i)
                      s
                    (modify
                     th s
                     :stack
                     (push (int-fix (+ i (top (stack (top-frame th s)))))
                           (pop (stack (top-frame th s))))))))
  :hints (("Goal"
           :induct (universal-loop-hint th s i)
           :in-theory (enable zp))))

(defun poised-to-invoke-universal (th s i)
  (and (equal (status th s) 'SCHEDULED)
       (equal (next-inst th s) '(INVOKESTATIC "Universal" "universal" 0))
       (equal (lookup-method "universal" "Universal" (class-table s))
              '("universal" NIL NIL
                (ICONST_0)
                (ICONST_1)
                (IADD)
                (GOTO -2)))
       (integerp i)
       (<= 0 i)))

(defun universal-sched (th i)
  (append (repeat th 2)
          (universal-loop-sched th i)))

(defthm universal-is-correct
  (implies (poised-to-invoke-universal th s i)
           (equal (top
                   (stack
                    (top-frame th
                               (run (universal-sched th i) s))))
                  (int-fix i))))

(in-theory (disable universal-sched))

; So now I want to prove that if k is an int, then k = (int-fix i),
; for some natural number i.  First I define the corresponding
; natural number:

(defun int-fix-nat (k)
  (cond ((< k 0)
         (+ (expt 2 32) k))
        (t k)))

; Here I prove it is a natural.

(defthm natp-int-fix-nat
  (implies (intp k)
           (and (integerp (int-fix-nat k))
                (<= 0 (int-fix-nat k))))
  :hints (("Goal" :in-theory (enable intp))))

; Here I prove it does the job.

(defthm every-int-is-int-fix-nat
  (implies (intp k)
           (equal (int-fix (int-fix-nat k)) k))
  :hints (("Goal" :in-theory (enable int-fix intp))))

(in-theory (disable int-fix-nat))

; Consequently, we can now prove that with a suitable schedule,
; universal computes our arbitrary int-valued function f.

(defun universal-schedule (x)
  (universal-sched 0 (int-fix-nat (f x))))

(defthm universal-computes-f
  (equal (top
          (stack
           (top-frame 0
                      (run (universal-schedule x)
                           *universal-state*))))
         (f x))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable top-frame))))

; Now I demonstrate that we can use it.  Here is a concrete example of
; how universal can compute the int-fix of factorial.  That value is
; what we proved of our true Java fact program.

(defun factorial (n)
  (if (zp n)
      1
    (* n (factorial (- n 1)))))

(defthm integerp-factorial
  (integerp (factorial n))
  :rule-classes :type-prescription)

(defun universal-factorial-schedule (n)
  (universal-sched 0 (int-fix-nat (int-fix (factorial n)))))

; Here I prove that (int-fix (factorial n)) satisfies the constraints
; on (f n).

(defthm relieve-the-contraints
  (and (integerp (int-fix (factorial n)))
       (>= (int-fix (factorial n)) (* -1 (expt 2 31)))
       (<= (int-fix (factorial n)) (1- (expt 2 31))))
  :rule-classes
  ((:linear :corollary
            (>= (int-fix (factorial n)) (* -1 (expt 2 31))))
   (:linear :corollary
            (<= (int-fix (factorial n)) (1- (expt 2 31)))))
  :hints (("Goal" :in-theory (enable int-fix))))

; And so now I can functionally instantiate our universal correctness
; theorem.

(defthm universal-computes-factorial
  (equal (top
          (stack
           (top-frame 0
                      (run (universal-factorial-schedule n)
                           *universal-state*))))
         (int-fix (factorial n)))
  :hints (("Goal"
           :use (:instance (:functional-instance
                            universal-computes-f
                            (f (lambda (n) (int-fix (factorial n))))
                            (universal-schedule universal-factorial-schedule))
                           (x n)))))
