; Copyright (C) 2001 J Strother Moore

; This book is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License as
; published by the Free Software Foundation; either version 2 of
; the License, or (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public
; License along with this book; if not, write to the Free
; Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139,
; USA.

; This book proves the correctness of a recursive static method
; for factorial on M5.

#|
Here is the Java for a factorial method.

class Demo {

    static int ans;

    public static int fact(int n) {
        if (n>0)
            return n*fact(n-1);
        else
            return 1;
    }

    /* Dummy main method */

    public static void main() {
        int k = 4;
        ans = fact(k+1);
    }

    /* This main method is not simulated */
    /* because our M5 model does not support the */
    /* native methods necessary to support IO. */

    public static void main(String[] args) {
        int n = Integer.parseInt(args[0], 10);
        System.out.println(fact(n));
    }
}

If you put this into Demo.java and run

% javac Demo.java
% javap -c Demo

you get the following:

Compiled from "Demo.java"
class Demo {
  static int ans;

  Demo();
    Code:
       0: aload_0
       1: invokespecial #1                  // Method java/lang/Object."<init>":()V
       4: return

  public static int fact(int);
    Code:
       0: iload_0
       1: ifle          13
       4: iload_0
       5: iload_0
       6: iconst_1
       7: isub
       8: invokestatic  #2                  // Method fact:(I)I
      11: imul
      12: ireturn
      13: iconst_1
      14: ireturn

  public static void main();
    Code:
       0: iconst_4
       1: istore_0
       2: iload_0
       3: iconst_1
       4: iadd
       5: invokestatic  #2                  // Method fact:(I)I
       8: putstatic     #3                  // Field ans:I
      11: return

  public static void main(java.lang.String[]);
    Code:
       0: aload_0
       1: iconst_0
       2: aaload
       3: bipush        10
       5: invokestatic  #4                  // Method java/lang/Integer.parseInt:(Ljava/lang/String;I)I
       8: istore_1
       9: getstatic     #5                  // Field java/lang/System.out:Ljava/io/PrintStream;
      12: iload_1
      13: invokestatic  #2                  // Method fact:(I)I
      16: invokevirtual #6                  // Method java/io/PrintStream.println:(I)V
      19: return
}

The output of jvm2acl2 for M5 is in classes/Demo.

|#

(in-package "M5")
(include-book "utilities")
(include-book "classes/Demo")

(defconst *Demo-class-table-in-tagged-form*
 (make-class-def
  (list
    *Demo*)))

(defconst *Demo-main*
  (method-program (bound? "main:()V" (class-decl-methods *Demo*))))

(defun Demo-ms ()
  (make-state
   (make-tt (push (make-frame 0
                              ()
                              ()
                              *Demo-main*
                              'unlocked
                              "Demo")
                  nil))
   nil
   *Demo-class-table-in-tagged-form*
   *default-m5-options*))

(defun Demo ()
  (m5_load (Demo-ms)))

; Here is the state created by (Demo):
#|
(((0 ((0 NIL NIL
         ((ICONST_4)
          (ISTORE_0)
          (ILOAD_0)
          (ICONST_1)
          (IADD)
          (INVOKESTATIC 2)
          (PUTSTATIC 3)
          (RETURN))
         UNLOCKED "Demo"))
     SCHEDULED NIL))
 ((0 ("java/lang/Class" ("<sfields>")
                        ("<name>" . "java/lang/Object"))
     ("java/lang/Object" ("<monitor>" . 0)
                         ("<mcount>" . 0)))
  (1 ("java/lang/Class" ("<sfields>")
                        ("<name>" . "[Ljava/lang/Object;"))
     ("java/lang/Object" ("<monitor>" . 0)
                         ("<mcount>" . 0)))
  (2 ("java/lang/Class" ("<sfields>")
                        ("<name>" . "[C"))
     ("java/lang/Object" ("<monitor>" . 0)
                         ("<mcount>" . 0)))
  (3 ("java/lang/Class" ("<sfields>")
                        ("<name>" . "java/lang/Thread"))
     ("java/lang/Object" ("<monitor>" . 0)
                         ("<mcount>" . 0)))
  (4 ("java/lang/Class" ("<sfields>")
                        ("<name>" . "java/lang/String"))
     ("java/lang/Object" ("<monitor>" . 0)
                         ("<mcount>" . 0)))
  (5 ("java/lang/Class" ("<sfields>")
                        ("<name>" . "[Ljava/lang/String;"))
     ("java/lang/Object" ("<monitor>" . 0)
                         ("<mcount>" . 0)))
  (6 ("java/lang/Class" ("<sfields>")
                        ("<name>" . "java/lang/Class"))
     ("java/lang/Object" ("<monitor>" . 0)
                         ("<mcount>" . 0)))
  (7 ("java/lang/Class" ("<sfields>" ("ans:I" . 0))
                        ("<name>" . "Demo"))
     ("java/lang/Object" ("<monitor>" . 0)
                         ("<mcount>" . 0))))
 (("java/lang/Object" NIL (NIL)
                      33 NIL (("<init>:()V" 1 (RETURN)))
                      (REF 0))
  ("[Ljava/lang/Object;" ("java/lang/Object")
                         NIL 0 NIL NIL (REF 1))
  ("[C" ("java/lang/Object")
        NIL 0 NIL NIL (REF 2))
  ("java/lang/Thread" ("java/lang/Object")
                      (NIL (METHODREF "java/lang/Object" "<init>:()V" 0))
                      33 NIL
                      (("run:()V" 1 (RETURN))
                       ("start:()V" 289)
                       ("stop:()V" 273)
                       ("<init>:()V" 1 (ALOAD_0)
                                     (INVOKESPECIAL 1)
                                     (RETURN)))
                      (REF 3))
  ("java/lang/String" ("java/lang/Object")
                      (NIL (METHODREF "java/lang/Object" "<init>:()V" 0))
                      49 (("value:[C" 18))
                      (("<init>:()V" 1 (ALOAD_0)
                                     (INVOKESPECIAL 1)
                                     (RETURN)))
                      (REF 4))
  ("[Ljava/lang/String;" ("[Ljava/lang/Object;" "java/lang/Object")
                         NIL 0 NIL NIL (REF 5))
  ("java/lang/Class" ("java/lang/Object")
                     (NIL (METHODREF "java/lang/Object" "<init>:()V" 0))
                     49 NIL
                     (("<init>:()V" 1 (ALOAD_0)
                                    (INVOKESPECIAL 1)
                                    (RETURN)))
                     (REF 6))
  ("Demo" ("java/lang/Object")
          (NIL (METHODREF "java/lang/Object" "<init>:()V" 0)
               (METHODREF "Demo" "fact:(I)I" 1)
               (FIELDREF "Demo" "ans:I" 1)
               (METHODREF "NoClassDefFoundError: java/lang/Integer"
                          "parseInt:(Ljava/lang/String;I)I" 2)
               (FIELDREF "NoClassDefFoundError: java/lang/System"
                         "out:Ljava/io/PrintStream;" 1)
               (METHODREF "NoClassDefFoundError: java/io/PrintStream"
                          "println:(I)V" 1)
               (CLASS (REF 7) "Demo")
               (CLASS (REF 0) "java/lang/Object")
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (NAME-AND-TYPE "<init>:()V")
               (NAME-AND-TYPE "fact:(I)I")
               (NAME-AND-TYPE "ans:I")
               (CLASS NIL
                      "NoClassDefFoundError: java/lang/Integer")
               (NAME-AND-TYPE "parseInt:(Ljava/lang/String;I)I")
               (CLASS NIL
                      "NoClassDefFoundError: java/lang/System")
               (NAME-AND-TYPE "out:Ljava/io/PrintStream;")
               (CLASS NIL
                      "NoClassDefFoundError: java/io/PrintStream")
               (NAME-AND-TYPE "println:(I)V")
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8)
               (UTF8))
          32 (("ans:I" 8))
          (("<init>:()V" 0 (ALOAD_0)
                         (INVOKESPECIAL 1)
                         (RETURN))
           ("fact:(I)I" 9 (ILOAD_0)
                        (IFLE 12)
                        (ILOAD_0)
                        (ILOAD_0)
                        (ICONST_1)
                        (ISUB)
                        (INVOKESTATIC 2)
                        (IMUL)
                        (IRETURN)
                        (ICONST_1)
                        (IRETURN))
           ("main:()V" 9 (ICONST_4)
                       (ISTORE_0)
                       (ILOAD_0)
                       (ICONST_1)
                       (IADD)
                       (INVOKESTATIC 2)
                       (PUTSTATIC 3)
                       (RETURN))
           ("main:([Ljava/lang/String;)V" 9 (ALOAD_0)
                                          (ICONST_0)
                                          (AALOAD)
                                          (BIPUSH 10)
                                          (INVOKESTATIC 4)
                                          (ISTORE_1)
                                          (GETSTATIC 5)
                                          (ILOAD_1)
                                          (INVOKESTATIC 2)
                                          (INVOKEVIRTUAL 6)
                                          (RETURN)))
          (REF 7)))
 DEFAULT-M5-OPTIONS)
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
               (ISTORE\_0)
               (ILOAD\_0)
               (ICONST\_1)
               (IADD)
               (INVOKESTATIC 2) ; Demo.fact:(I)I
               (PUTSTATIC 3) ; Demo.ans:I
               (RETURN))
             'UNLOCKED
             "Demo")
            nil)
           'SCHEDULED
           nil))))

(defconst *Demo-heap*
  '((0 . (("java/lang/Class" ("<sfields>") ("<name>" . "java/lang/Object"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (1 . (("java/lang/Class" ("<sfields>") ("<name>" . "[Ljava/lang/Object;"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (2 . (("java/lang/Class" ("<sfields>") ("<name>" . "[C"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (3 . (("java/lang/Class"  ("<sfields>") ("<name>" . "java/lang/Thread"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (4 . (("java/lang/Class" ("<sfields>") ("<name>" . "java/lang/String"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (5 . (("java/lang/Class" ("<sfields>") ("<name>" . "[Ljava/lang/String;"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (6 . (("java/lang/Class" ("<sfields>") ("<name>" . "java/lang/Class"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (7 . (("java/lang/Class"
           ("<sfields>"
            ("ans:I" . 0))
           ("<name>" . "Demo"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))))

(defconst *Demo-class-table*
  '(("java/lang/Object"
     ()
     (NIL)
     #x00000021                                                ;  ACC_PUBLIC ACC_SUPER
     ()
     (("<init>:()V" #x00000001                                 ;  ACC_PUBLIC
       (RETURN)))
     (REF 0))
    ("[Ljava/lang/Object;"
     ("java/lang/Object")
     ()
     0
     ()
     ()
     (REF 1))
    ("[C"
     ("java/lang/Object")
     ()
     0
     ()
     ()
     (REF 2))
    ("java/lang/Thread"
     ("java/lang/Object")
     (NIL (METHODREF "java/lang/Object" "<init>:()V" 0))
     #x00000021                                                ;  ACC_PUBLIC ACC_SUPER
     ()
     (("run:()V" #x00000001                                    ;  ACC_PUBLIC
       (RETURN))
      ("start:()V" #x00000121)                                 ;  ACC_PUBLIC ACC_SYNCHRONIZED ACC_NATIVE
      ("stop:()V" #x00000111)                                  ;  ACC_PUBLIC ACC_FINAL ACC_NATIVE
      ("<init>:()V" #x00000001                                 ;  ACC_PUBLIC
       (ALOAD\_0)
       (INVOKESPECIAL 1)
       (RETURN)))
     (REF 3))
    ("java/lang/String"
     ("java/lang/Object")
     (NIL (METHODREF "java/lang/Object" "<init>:()V" 0))
     #x00000031                                                ;  ACC_PUBLIC ACC_FINAL ACC_SUPER
     (
      ("value:[C" #x00000012)                                 ;  ACC_PRIVATE ACC_FINAL
     )
     (("<init>:()V" #x00000001                                 ;  ACC_PUBLIC
       (ALOAD\_0)
       (INVOKESPECIAL 1)
       (RETURN)))
     (REF 4))
    ("[Ljava/lang/String;"
     ("[Ljava/lang/Object;" "java/lang/Object")
     ()
     0
     ()
     ()
     (REF 5))
    ("java/lang/Class"
     ("java/lang/Object")
     (NIL (METHODREF "java/lang/Object" "<init>:()V" 0))
     #x00000031                                                ;  ACC_PUBLIC ACC_FINAL ACC_SUPER
     ()
     (("<init>:()V" #x00000001                                 ;  ACC_PUBLIC
       (ALOAD\_0)
       (INVOKESPECIAL 1)
       (RETURN)))
     (REF 6))
    ("Demo"
     ("java/lang/Object")
     (nil
       (methodref "java/lang/Object" "<init>:()V" 0)           ; 1
       (methodref "Demo" "fact:(I)I" 1)                        ; 2
       (fieldref "Demo" "ans:I" 1)                             ; 3
       (methodref "NoClassDefFoundError: java/lang/Integer" "parseInt:(Ljava/lang/String;I)I" 2) ; 4
       (fieldref "NoClassDefFoundError: java/lang/System" "out:Ljava/io/PrintStream;" 1) ; 5
       (methodref "NoClassDefFoundError: java/io/PrintStream" "println:(I)V" 1) ; 6
       (class (ref 7) "Demo")                                  ; 7
       (class (ref 0) "java/lang/Object")                      ; 8
       (utf8)                                                  ; 9
       (utf8)                                                  ; 10
       (utf8)                                                  ; 11
       (utf8)                                                  ; 12
       (utf8)                                                  ; 13
       (utf8)                                                  ; 14
       (utf8)                                                  ; 15
       (utf8)                                                  ; 16
       (utf8)                                                  ; 17
       (utf8)                                                  ; 18
       (utf8)                                                  ; 19
       (utf8)                                                  ; 20
       (utf8)                                                  ; 21
       (name-and-type "<init>:()V")                            ; 22
       (name-and-type "fact:(I)I")                             ; 23
       (name-and-type "ans:I")                                 ; 24
       (class nil "NoClassDefFoundError: java/lang/Integer")   ; 25
       (name-and-type "parseInt:(Ljava/lang/String;I)I")       ; 26
       (class nil "NoClassDefFoundError: java/lang/System")    ; 27
       (name-and-type "out:Ljava/io/PrintStream;")             ; 28
       (class nil "NoClassDefFoundError: java/io/PrintStream") ; 29
       (name-and-type "println:(I)V")                          ; 30
       (utf8)                                                  ; 31
       (utf8)                                                  ; 32
       (utf8)                                                  ; 33
       (utf8)                                                  ; 34
       (utf8)                                                  ; 35
       (utf8)                                                  ; 36
       (utf8)                                                  ; 37
       (utf8)                                                  ; 38
       (utf8)                                                  ; 39
       (utf8)                                                  ; 40
       (utf8)                                                  ; 41
      )
     #x00000020                                                ;  ACC_SUPER
     (
       ("ans:I" #x00000008)                                    ;  ACC_STATIC
     )
     (("<init>:()V" #x00000000                                 ;
       (ALOAD\_0)
       (INVOKESPECIAL 1)
       (RETURN))
      ("fact:(I)I" #x00000009                                  ;  ACC_PUBLIC ACC_STATIC
       (ILOAD\_0)
       (IFLE 12)
       (ILOAD\_0)
       (ILOAD\_0)
       (ICONST\_1)
       (ISUB)
       (INVOKESTATIC 2) ; Demo.fact:(I)I
       (IMUL)
       (IRETURN)
       (ICONST\_1)
       (IRETURN))
      ("main:()V" #x00000009                                   ;  ACC_PUBLIC ACC_STATIC
       (ICONST_4)
       (ISTORE_0)
       (ILOAD_0)
       (ICONST_1)
       (IADD)
       (INVOKESTATIC 2) ; Demo.fact:(I)I
       (PUTSTATIC 3) ; Demo.ans:I
       (RETURN))
      ("main:([Ljava/lang/String;)V" #x00000009                ;  ACC_PUBLIC ACC_STATIC
       (ALOAD_0)
       (ICONST_0)
       (AALOAD)
       (BIPUSH 10)
       (INVOKESTATIC 4) ; NoClassDefFoundError: java.lang.Integer.parseInt:(Ljava/lang/String;I)I
       (ISTORE_1)
       (GETSTATIC 5) ; NoClassDefFoundError: java.lang.System.out:Ljava/io/PrintStream;
       (ILOAD_1)
       (INVOKESTATIC 2) ; Demo.fact:(I)I
       (INVOKEVIRTUAL 6)
       (RETURN)))
     (REF 7))))

(defconst *Demo-state*
  (make-state *demo-thread-table*
              *demo-heap*
              *demo-class-table*
              *default-m5-options*))

(defthm demo-state-is-demo
  (equal (Demo)
         *Demo-state*)
  :rule-classes nil)

; The Mathematical Function

(defun ! (n)
  (if (zp n)
      1
    (* n (! (- n 1)))))

(defthm integerp-factorial
  (integerp (! n))
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
  (equal (static-field-value "Demo" "ans:I"
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
       "Demo" "ans:I"
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
                         (INVOKESTATIC 2) ;  Demo.fact:(I)I
                         (PUTSTATIC 3) ; Demo.ans:I
                         (RETURN))
                       'UNLOCKED
                       "Demo")
                      nil)
                     'SCHEDULED
                     nil)))
             *demo-heap*
             *demo-class-table*
             *default-m5-options*)))))))
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
      '("fact:(I)I" #x00000009                                  ;  ACC_PUBLIC ACC_STATIC
        ; line_number #6
        (iload_0)                                               ; 0
        (ifle 12)                                               ; 1
        ; line_number #7
        (iload_0)                                               ; 4
        (iload_0)                                               ; 5
        (iconst_1)                                              ; 6
        (isub)                                                  ; 7
        (invokestatic 2)                                        ; 8
        (imul)                                                  ; 11
        (ireturn)                                               ; 12
        ; line_number #9
        (iconst_1)                                              ; 13
        (ireturn)))                                             ; 14

(defun poised-to-invoke-fact (th s n)
  (and (poised-to-invokestatic th s "Demo" "fact:(I)I" 1)
       (equal (retrieve-cp-entry "Demo" 2 (class-table s))
              '(methodref "Demo" "fact:(I)I" 1))
       (equal n (top (stack (top-frame th s))))
       (intp n)
       (equal (bound? "fact:(I)I" (class-decl-methods (bound? "Demo" (class-table s))))
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
      (class-table s)
      (options s))
     (- n 1))))

; The make-state in the induction-hint above is equivalent to
; (run (repeat th 7) s), under the hypotheses that s is poised to
; invoke fact and that n is non-0.  We prove that below, just to
; demonstrate this claim.  The import of this claim is that we
; could use this to help generate the induction hint, i.e., the
; make-state is not "magic."  Indeed, the theorem below is
; generated by the following forms:

#||
(include-book "misc/expander" :dir :system)
(acl2::defthm? induction-hint-explanation
               (implies (and (poised-to-invoke-fact th s n)
                             (not (zp n)))
                        (equal (run (repeat th 7) s)
                               acl2::?)))
||#

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
                       (list n)
                       (push (+ -1 n)
                             (push n
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
                   (class-table s)
                   (options s))))
  :rule-classes nil)
