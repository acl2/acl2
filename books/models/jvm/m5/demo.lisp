; This book proves the correctness of a recursive static method
; for factorial on M5.

#|
; Certification Instructions.

(include-book "utilities")

(certify-book "demo" 1)

J Moore

Here is the Java for a factorial method.

class Demo {

  static int ans;

  public static int fact(int n){
    if (n>0)
      {return n*fact(n-1);}
    else return 1;
  }

  public static void main(String[] args){
  int k = 4;
  ans = fact(k+1);
  return;
  }
 }

If you put this into Demo.java and run

% javac Demo.java
% javap -o Demo

you get the following:

Compiled from Demo.java
synchronized class Demo extends java.lang.Object
    /* ACC_SUPER bit set */
{
    static int ans;
    public static int fact(int);
    public static void main(java.lang.String[]);
    Demo();
}

Method int fact(int)
   0 iload_0
   1 ifle 13
   4 iload_0
   5 iload_0
   6 iconst_1
   7 isub
   8 invokestatic #5 <Method int fact(int)>
  11 imul
  12 ireturn
  13 iconst_1
  14 ireturn

Method void main(java.lang.String[])
   0 iconst_4
   1 istore_1
   2 iload_1
   3 iconst_1
   4 iadd
   5 invokestatic #5 <Method int fact(int)>
   8 putstatic #4 <Field int ans>
  11 return

Method Demo()
   0 aload_0
   1 invokespecial #3 <Method java.lang.Object()>
   4 return

Below is the output of jvm2acl2 for M5.

|#

(in-package "M5")

(defconst *Demo-class-table-in-tagged-form*
 (make-class-def
  (list
    (make-class-decl
     "Demo"
     '("java.lang.Object")
     '()
     '("ans")
     '()
     (list
      '("<init>" () nil
        (aload_0)
        (invokespecial "java.lang.Object" "<init>" 0)
        (return))
      '("fact" (int) nil
        (iload_0)
        (ifle LABEL::TAG_0)
        (iload_0)
        (iload_0)
        (iconst_1)
        (isub)
        (invokestatic "Demo" "fact" 1)
        (imul)
        (ireturn)
        (LABEL::TAG_0 iconst_1)
        (ireturn))
      '("main" (java.lang.String[]) nil
        (iconst_4)
        (istore_1)
        (iload_1)
        (iconst_1)
        (iadd)
        (invokestatic "Demo" "fact" 1)
        (putstatic "Demo" "ans" nil)
        (return)))
     '(REF -1)))))

(defconst *Demo-main*
  '((iconst_4)
    (istore_1)
    (iload_1)
    (iconst_1)
    (iadd)
    (invokestatic "Demo" "fact" 1)
    (putstatic "Demo" "ans" nil)
    (return)))

(defun Demo-ms ()
  (make-state
   (make-tt (push (make-frame 0
                              nil
                              nil
                              *Demo-main*
                              'UNLOCKED
                              "Demo")
                  nil))
   nil
   *Demo-class-table-in-tagged-form*))

(defun Demo ()
  (m5_load (Demo-ms)))

; Here is the state created by (Demo):
#|
(((0 ((0 NIL NIL
         ((ICONST_4)
          (ISTORE_1)
          (ILOAD_1)
          (ICONST_1)
          (IADD)
          (INVOKESTATIC "Demo" "fact" 1)
          (PUTSTATIC "Demo" "ans" NIL)
          (RETURN))
         UNLOCKED "Demo"))
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
  (5 ("java.lang.Class" ("<name>" . "Demo")
      ("ans" . 0))
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
  ("Demo" ("java.lang.Object")
   NIL ("ans")
   NIL
   (("<init>" NIL NIL (ALOAD_0)
     (INVOKESPECIAL "java.lang.Object" "<init>" 0)
     (RETURN))
    ("fact" (INT)
     NIL (ILOAD_0)
     (IFLE 12)
     (ILOAD_0)
     (ILOAD_0)
     (ICONST_1)
     (ISUB)
     (INVOKESTATIC "Demo" "fact" 1)
     (IMUL)
     (IRETURN)
     (ICONST_1)
     (IRETURN))
    ("main" (|JAVA.LANG.STRING[]|)
     NIL (ICONST_4)
     (ISTORE_1)
     (ILOAD_1)
     (ICONST_1)
     (IADD)
     (INVOKESTATIC "Demo" "fact" 1)
     (PUTSTATIC "Demo" "ans" NIL)
     (RETURN)))
   (REF 5))))
|#

; But in the paper we discuss it component by component and
; define constants for each.  Note that we can write ICONST_4 or
; ICONST\_4 in Common Lisp.  We use the latter so that we can
; pick these forms up and dump them into LaTeX.

(defconst *Demo-thread-table*
   (list
    (cons 0
          (make-thread
           (push
            (make-frame
             0
             nil
             nil
             '((ICONST\_4)
               (ISTORE\_1)
               (ILOAD\_1)
               (ICONST\_1)
               (IADD)
               (INVOKESTATIC "Demo" "fact" 1)
               (PUTSTATIC "Demo" "ans" NIL)
               (RETURN))
             'UNLOCKED
             "Demo")
            nil)
           'SCHEDULED
           nil))))

(defconst *Demo-heap*
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
           ("<name>" . "Demo")
           ("ans" . 0))
          ("java.lang.Object"
           ("monitor" . 0)
           ("mcount" . 0)
           ("wait-set" . 0))))))

(defconst *Demo-class-table*
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
    ("Demo"
     ("java.lang.Object")
     NIL
     ("ans")
     NIL
     (("<init>" NIL NIL
       (ALOAD\_0)
       (INVOKESPECIAL "java.lang.Object" "<init>" 0)
       (RETURN))
      ("fact" (INT) NIL
       (ILOAD\_0)
       (IFLE 12)
       (ILOAD\_0)
       (ILOAD\_0)
       (ICONST\_1)
       (ISUB)
       (INVOKESTATIC "Demo" "fact" 1)
       (IMUL)
       (IRETURN)
       (ICONST\_1)
       (IRETURN))
      ("main" (|JAVA.LANG.STRING[]|) NIL
       (ICONST\_4)
       (ISTORE\_1)
       (ILOAD\_1)
       (ICONST\_1)
       (IADD)
       (INVOKESTATIC "Demo" "fact" 1)
       (PUTSTATIC "Demo" "ans" NIL)
       (RETURN)))
     (REF 5))))

(defconst *Demo-state*
  (make-state *demo-thread-table*
              *demo-heap*
              *demo-class-table*))

(defthm demo-state-is-demo
  (equal (Demo)
         *Demo-state*)
  :rule-classes nil)

; The Mathematical Function

(defun factorial (n)
  (if (zp n)
      1
    (* n (factorial (- n 1)))))

(defthm integerp-factorial
  (integerp (factorial n))
  :rule-classes :type-prescription)

; A Schedule that Runs fact to Completion

(defun fact-sched (th n)
  (if (zp n)
      (repeat th 5)
    (append (repeat th 7)
            (fact-sched th (- n 1))
            (repeat th 2))))

(defthm len-repeat
  (equal (len (repeat th n)) (nfix n)))

(defthm len-append
  (equal (len (append a b))
         (+ (len a) (len b))))

(defthm len-fact-sched
  (equal (len (fact-sched th n))
         (+ 5 (* 9 (nfix n)))))

; Playing Around with Main

; This schedule executes main to termination.

(defun main-sched (th)
  (append (repeat th 5)
          (fact-sched th 5)
          (repeat th 2)))

(defthm sample-execution
  (equal (static-field-value "Demo" "ans"
                             (run (main-sched 0) *Demo-state*))
         120)
  :rule-classes nil)

#|

; Below is a fact-test function.  I define it in raw Lisp rather
; than ACL2 so that I can time the execution of the JVM model
; without timing the construction of the schedule.  To define
; this function, exit the loop with :q and do these two forms.

(in-package "M5")
(compile
 (defun fact-test (n)
   (format t "Computing schedule for ~a.~%" n)
   (let ((sched (append (repeat 0 1)
                        (fact-sched 0 n)
                        (repeat 0 2))))
     (format t "Schedule length:  ~a.~%" (len sched))
     (time
      (static-field-value
       "Demo" "ans"
       (run sched
            (make-state
             (list
              (cons 0
                    (make-thread
                     (push
                      (make-frame
                       0
                       (list n)
                       nil
                       '((ILOAD\_0)
                         (INVOKESTATIC "Demo" "fact" 1)
                         (PUTSTATIC "Demo" "ans" NIL)
                         (RETURN))
                       'UNLOCKED
                       "Demo")
                      nil)
                     'SCHEDULED
                     nil)))
             *demo-heap*
             *demo-class-table*)))))))
; Allocate additional bignum space
(si::allocate 'lisp::bignum 400 t)
T

; Then do things like (fact-test 17) or (fact-test 1000).  On a 797
; MHz Pentium III, the latter requires a schedule of length 9008 and
; takes 0.100 seconds to execute, provided no (BIGNUM) gcs occur.
; This gives a simulation speed of 90K JVM bytecodes per second.

|#

; Proving Fact Correct

(defconst *fact-def*
  '("fact" (INT) NIL
    (ILOAD_0)                         ;;;  0
    (IFLE 12)                         ;;;  1
    (ILOAD_0)                         ;;;  4
    (ILOAD_0)                         ;;;  5
    (ICONST_1)                        ;;;  6
    (ISUB)                            ;;;  7
    (INVOKESTATIC "Demo" "fact" 1)    ;;;  8
    (IMUL)                            ;;; 11
    (IRETURN)                         ;;; 12
    (ICONST_1)                        ;;; 13
    (IRETURN)))                       ;;; 14

(defun poised-to-invoke-fact (th s n)
  (and (equal (status th s) 'SCHEDULED)
       (equal (next-inst th s) '(invokestatic "Demo" "fact" 1))
       (equal n (top (stack (top-frame th s))))
       (intp n)
       (equal (lookup-method "fact" "Demo" (class-table s))
              *fact-def*)))

(defun induction-hint (th s n)
  (if (zp n)
      s
    (induction-hint
     th
     (make-state                 ;;; (run (repeat th 7) s)
      (bind
       th
       (make-thread
        (push
         (make-frame
          8
          (list (top (stack (top-frame th s))))
          (push (- (top (stack (top-frame th s))) 1)
                (push (top (stack (top-frame th s)))
                      nil))
          (method-program *fact-def*)
          'UNLOCKED
          "Demo")
         (push (make-frame (+ 3 (pc (top (call-stack th s))))
                           (locals (top (call-stack th s)))
                           (pop (stack (top (call-stack th s))))
                           (program (top (call-stack th s)))
                           (sync-flg (top (call-stack th s)))
                           (cur-class (top (call-stack th s))))
               (pop (call-stack th s))))
        'scheduled
        (rref th s))
       (thread-table s))
      (heap s)
      (class-table s))
     (- n 1))))

; The make-state in the induction-hint above is equivalent to
; (run (repeat th 7) s), under the hypotheses that s is poised to
; invoke fact and that n is non-0.  We prove that below, just to
; demonstrate this claim.  The import of this claim is that we
; could use this to help generate the induction hint, i.e., the
; make-state is not "magic."

(defthm induction-hint-explanation
  (implies (and (poised-to-invoke-fact th s n)
                (not (zp n)))
           (equal (run (repeat th 7) s)
                  (make-state                 ;;; (run (repeat th 7) s)
                   (bind
                    th
                    (make-thread
                     (push
                      (make-frame
                       8
                       (list (top (stack (top-frame th s))))
                       (push (- (top (stack (top-frame th s))) 1)
                             (push (top (stack (top-frame th s)))
                                   nil))
                       (method-program *fact-def*)
                       'UNLOCKED
                       "Demo")
                      (push (make-frame (+ 3 (pc (top (call-stack th s))))
                                        (locals (top (call-stack th s)))
                                        (pop (stack (top (call-stack th s))))
                                        (program (top (call-stack th s)))
                                        (sync-flg (top (call-stack th s)))
                                        (cur-class (top (call-stack th s))))
                            (pop (call-stack th s))))
                     'scheduled
                     (rref th s))
                    (thread-table s))
                   (heap s)
                   (class-table s))))
  :rule-classes nil)

(defthm fact-is-correct
  (implies (poised-to-invoke-fact th s n)
           (equal
            (run (fact-sched th n) s)
            (modify th s
             :pc (+ 3 (pc (top-frame th s)))
             :stack (push (int-fix (factorial n))
                          (pop (stack (top-frame th s)))))))
  :hints (("Goal"
           :induct (induction-hint th s n))))

(in-theory (disable fact-sched))

(defthm weak-version-of-fact-is-correct
  (implies (poised-to-invoke-fact th s n)
           (equal (top
                   (stack
                    (top-frame
                     th
                     (run (fact-sched th n) s))))
                  (int-fix (factorial n)))))

; Symbolic Computation and Use of fact as a Subroutine

(defthm symbolic-computation
  (implies
   (intp (+ 1 k))
   (equal
    (nth 3
         (locals
          (top-frame 0
           (run (append (repeat 0 4)
                        (fact-sched 0 (+ 1 k))
                        (repeat 0 2))
                (make-state
                 (make-tt
                  (push
                   (make-frame 0
                               (list v0 v1 v2 k)
                               stk
                               '((iconst_2)
                                 (iload_3)
                                 (iconst_1)
                                 (iadd)
                                 (invokestatic "Demo" "fact" 1)
                                 (imul)
                                 (istore_3))
                               'UNLOCKED
                               "Test")
                   nil))
                 *demo-heap*
                 *demo-class-table*)))))

    (int-fix (* 2 (factorial (+ 1 k)))))))

; In the steps below we demonstrate the key steps in the
; simplification above, to check the claims made in the paper.

(defun alpha (pc locals stk)
  (make-state
   (make-tt
    (push (make-frame pc
                      locals
                      stk
                      '((iconst_2)
                        (iload_3)
                        (iconst_1)
                        (iadd)
                        (invokestatic "Demo" "fact" 1)
                        (imul)
                        (istore_3))
                      'UNLOCKED
                      "Test")
          nil))
   *demo-heap*
   *demo-class-table*))

(defthm symbolic-computation-step1
  (implies
   (intp (+ 1 k))
   (equal (run (append (repeat 0 4)
                       (fact-sched 0 (+ 1 k))
                       (repeat 0 2))
               (alpha 0 (list v0 v1 v2 k) stk))
          (run (repeat 0 2)
               (run (fact-sched 0 (+ 1 k))
                    (run (repeat 0 4)
                         (alpha 0 (list v0 v1 v2 k) stk)))))))

(defthm symbolic-computation-step2
  (implies
   (intp (+ 1 k))
   (equal (run (repeat 0 4)
               (alpha 0 (list v0 v1 v2 k) stk))
          (alpha 4 (list v0 v1 v2 k)
                 (push (+ 1 k) (push 2 stk))))))

(defthm symbolic-computation-step3
  (implies
   (intp (+ 1 k))
   (equal (run (fact-sched 0 (+ 1 k))
               (alpha 4 (list v0 v1 v2 k)
                      (push (+ 1 k) (push 2 stk))))
          (alpha 7 (list v0 v1 v2 k)
                 (push (int-fix (factorial (+ 1 k)))
                       (push 2 stk))))))


(defthm symbolic-computation-step4
  (implies
   (intp (+ 1 k))
   (equal (run (repeat 0 2)
               (alpha 7 (list v0 v1 v2 k)
                      (push (int-fix (factorial (+ 1 k)))
                            (push 2 stk))))
          (alpha 9 (list v0 v1 v2
                         (int-fix
                          (* 2 (factorial (+ 1 k))))) stk))))

