; This book proves the correctness of a recursive static method for
; factorial on M5.

#|
; Certification Instructions.

(include-book "utilities")

(certify-book "idemo" 1)

J Moore

Here is the Java for an iterative factorial method.

class IDemo {

  public static int ifact(int n){
    int temp = 1;
    while (0<n) {
	temp = n*temp;
	n = n-1;
    }
    return temp;
  }
 }

The corresponding bytecode for ifact is shown below.

Method int ifact(int)
   0 iconst_1
   1 istore_1
   2 goto 13
   5 iload_0
   6 iload_1
   7 imul
   8 istore_1
   9 iload_0
  10 iconst_1
  11 isub
  12 istore_0
  13 iload_0
  14 ifgt 5
  17 iload_1
  18 ireturn

|#

(in-package "M5")

; Note that we have not shown a main program for our IDemo
; class.  We make one up below.  The initial state is only used to
; play around.  We don't care about the main program when we prove
; ifact correct.

(defconst *IDemo-thread-table*
   (list
    (cons 0
          (make-thread
           (push
            (make-frame
             0
             nil
             nil
             '((ICONST\_4)
               (ICONST\_4)
               (IADD)
               (INVOKESTATIC "IDemo" "ifact" 1)
               (HALT))
             'UNLOCKED
             "IDemo")
            nil)
           'SCHEDULED
           nil))))

(defconst *IDemo-heap*
  '((0 . (("java.lang.Class"
           ("<name>" . "java.lang.Object"))
          ("java.lang.Object"
           ("monitor" . 0)
           ("mcount" . 0)
           ("wait-set" . 0))))
    (1 . (("java.lang.Class"
           ("<name>" . "ARRAY"))
          ("java.lang.Object"
           ("monitor" . 0)
           ("mcount" . 0)
           ("wait-set" . 0))))
    (2 . (("java.lang.Class"
           ("<name>" . "java.lang.Thread"))
          ("java.lang.Object"
           ("monitor" . 0)
           ("mcount" . 0)
           ("wait-set" . 0))))
    (3 . (("java.lang.Class"
           ("<name>" . "java.lang.String"))
          ("java.lang.Object"
           ("monitor" . 0)
           ("mcount" . 0)
           ("wait-set" . 0))))
    (4 . (("java.lang.Class"
           ("<name>" . "java.lang.Class"))
          ("java.lang.Object"
           ("monitor" . 0)
           ("mcount" . 0)
           ("wait-set" . 0))))
    (5 . (("java.lang.Class"
           ("<name>" . "IDemo"))
          ("java.lang.Object"
           ("monitor" . 0)
           ("mcount" . 0)
           ("wait-set" . 0))))))

(defconst *IDemo-class-table*
  '(("java.lang.Object"
     NIL
     ("monitor" "mcount" "wait-set")
     NIL
     NIL
     (("<init>" NIL NIL (RETURN)))
     (REF 0))
    ("ARRAY"
     ("java.lang.Object")
     (("<array>" . *ARRAY*))
     NIL
     NIL
     NIL
     (REF 1))
    ("java.lang.Thread"
     ("java.lang.Object")
     NIL
     NIL
     NIL
     (("run" NIL NIL (RETURN))
      ("start" NIL NIL NIL)
      ("stop" NIL NIL NIL)
      ("<init>" NIL NIL (ALOAD\_0)
       (INVOKESPECIAL "java.lang.Object" "<init>" 0)
       (RETURN)))
     (REF 2))
    ("java.lang.String"
     ("java.lang.Object")
     ("strcontents")
     NIL
     NIL
     (("<init>" NIL NIL
       (ALOAD\_0)
       (INVOKESPECIAL "java.lang.Object" "<init>" 0)
       (RETURN)))
     (REF 3))
    ("java.lang.Class"
     ("java.lang.Object")
     NIL
     NIL
     NIL
     (("<init>" NIL NIL
       (ALOAD\_0)
       (INVOKESPECIAL "java.lang.Object" "<init>" 0)
       (RETURN)))
     (REF 4))
    ("IDemo"
     ("java.lang.Object")
     NIL
     NIL
     NIL
     (("<init>" NIL NIL
       (ALOAD\_0)
       (INVOKESPECIAL "java.lang.Object" "<init>" 0)
       (RETURN))
      ("ifact" (INT) NIL
       (ICONST\_1)
       (ISTORE\_1)
       (GOTO 11)
       (ILOAD\_0)
       (ILOAD\_1)
       (IMUL)
       (ISTORE\_1)
       (ILOAD\_0)
       (ICONST\_1)
       (ISUB)
       (ISTORE\_0)
       (ILOAD\_0)
       (IFGT -9)
       (ILOAD\_1)
       (IRETURN)))
     (REF 5))))

(defconst *IDemo-state*
  (make-state *IDemo-thread-table*
              *IDemo-heap*
              *IDemo-class-table*))

; The Mathematical Function

(defun factorial (n)
  (if (zp n)
      1
    (* n (factorial (- n 1)))))

(defthm integerp-factorial
  (integerp (factorial n))
  :rule-classes :type-prescription)

; A Schedule that Runs fact to Completion

; This subroutine computes a schedule suitable for starting at the
; (ILOAD_0) at pc 13, which we consider the "top" of the loop.  The
; schedule drives the machine to (but not through) the (IRETURN).

(defun ifact-loop-sched (th n)
  (if (zp n)
      (repeat th 3)
    (append (repeat th 10)
            (ifact-loop-sched th (- n 1)))))

(defun ifact-sched (th n)
  (append (repeat th 4)
          (ifact-loop-sched th n)
          (repeat th 1)))

; Playing Around with Main

; This schedule executes main to termination.

(defun imain-sched (th)
  (append (repeat th 3)
          (ifact-sched th 8)))

(defthm isample-execution
  (equal (top
          (stack
           (top-frame 0
                      (run (imain-sched 0)
                           *IDemo-state*))))
         (factorial 8))
  :rule-classes nil)

; Proving Fact Correct

(defun ifactorial (n temp)
  (if (zp n)
      temp
    (ifactorial (- n 1) (int-fix (* n temp)))))

(defconst *ifact-def*
  (lookup-method "ifact" "IDemo" *IDemo-class-table*))

(defun poised-at-ifact-loop (th s n)
  (and (equal (status th s) 'SCHEDULED)
       (equal (pc (top-frame th s)) 13)
       (equal (program (top-frame th s)) (method-program *ifact-def*))
       (equal n (nth 0 (locals (top-frame th s))))
       (intp n)
       (intp (nth 1 (locals (top-frame th s))))))

(defun ifact-loop-induction-hint (th s n)
  (if (zp n)
      s
    (ifact-loop-induction-hint
     th
     (make-state
      (bind
       th
       (make-thread
        (push
         (make-frame 13
                     (update-nth 0 (- n 1)
                                 (update-nth 1 (int-fix
                                                (* n
                                                   (nth 1 (locals
                                                           (top-frame th s)))))
                                             (locals (top-frame th s))))
                     (stack (top-frame th s))
                     (method-program *ifact-def*)
                     (sync-flg (top-frame th s))
                     (cur-class (top-frame th s)))
         (pop (call-stack th s)))
        'scheduled
        (rref th s))
       (thread-table s))
      (heap s)
      (class-table s))
     (- n 1))))

(defthm ifact-loop-is-correct
  (implies (poised-at-ifact-loop th s n)
           (equal
            (run (ifact-loop-sched th n) s)
            (modify th s
             :pc 18
             :locals
             (if (zp n)
                 (locals (top-frame th s))
               (update-nth 0 0
                (update-nth 1
                            (int-fix
                             (ifactorial
                              n
                              (nth 1 (locals (top-frame th s)))))
                            (locals (top-frame th s)))))
             :stack
             (push (int-fix
                    (ifactorial
                     n
                     (nth 1 (locals (top-frame th s)))))
                   (stack (top-frame th s))))))
  :hints (("Goal"
           :induct (ifact-loop-induction-hint th s n))))

(defun poised-to-invoke-ifact (th s n)
  (and (equal (status th s) 'SCHEDULED)
       (equal (next-inst th s) '(invokestatic "IDemo" "ifact" 1))
       (equal n (top (stack (top-frame th s))))
       (intp n)
       (equal (lookup-method "ifact" "IDemo" (class-table s))
              *ifact-def*)))

(defthm ifact-is-correct
  (implies (poised-to-invoke-ifact th s n)
           (equal
            (run (ifact-sched th n) s)
            (modify th s
                    :pc (+ 3 (pc (top-frame th s)))
                    :stack
                    (push (int-fix (ifactorial n 1))
                          (pop (stack (top-frame th s))))))))

(in-theory (disable ifact-sched))

(defthm ifact-is-fact
  (implies (and (integerp n)
                (integerp temp))
           (equal (int-fix (ifactorial n temp))
                  (int-fix (* temp (factorial n))))))

(defthm ifact-main-result
  (implies (poised-to-invoke-ifact th s n)
           (equal
            (run (ifact-sched th n) s)
            (modify th s
                    :pc (+ 3 (pc (top-frame th s)))
                    :stack
                    (push (int-fix (factorial n))
                          (pop (stack (top-frame th s))))))))

