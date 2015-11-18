; Copyright (C) 2001 J Strother Moore

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; This book proves the correctness of a recursive static method for
; factorial on M5.

#|
Here is the Java for an iterative factorial method.

class IDemo {

    public static int ifact(int n) {
        int temp = 1;
        while (0<n) {
            temp = n*temp;
	    n = n-1;
        }
        return temp;
    }

    public static void main(Strig[] args) {
        ifact(8);
    }
}

The corresponding bytecode for ifact is shown below.

Compiled from "IDemo.java"
class IDemo {
  IDemo();
    Code:
       0: aload_0
       1: invokespecial #1                  // Method java/lang/Object."<init>":()V
       4: return

  public static int ifact(int);
    Code:
       0: iconst_1
       1: istore_1
       2: iconst_0
       3: iload_0
       4: if_icmpge     18
       7: iload_0
       8: iload_1
       9: imul
      10: istore_1
      11: iload_0
      12: iconst_1
      13: isub
      14: istore_0
      15: goto          2
      18: iload_1
      19: ireturn

  public static void main(java.lang.String[]);
    Code:
       0: bipush        8
       2: invokestatic  #2                  // Method ifact:(I)I
       5: pop
       6: return
}
|#

(in-package "M5")
(include-book "utilities")

(include-book "classes/IDemo")

(defconst *IDemo-class-table-in-tagged-form*
 (make-class-def
  (list
    *IDemo*)))

(defconst *IDemo-main*
  (method-program
    (bound? "main:([Ljava/lang/String;)V" (class-decl-methods *IDemo*))))

(defun IDemo-ms ()
  (make-state
   (make-tt (push (make-frame 0
                              nil
                              nil
                              *IDemo-main*
                              'UNLOCKED
                              "IDemo")
                  nil))
   nil
   *IDemo-class-table-in-tagged-form*
   *default-m5-options*))

(defun IDemo ()
  (m5_load (IDemo-ms)))

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
             '((bipush 8)
               (invokestatic "IDemo" "ifact:(I)I" 1)
               (pop)
               (return))
             'unlocked
             "IDemo")
            nil)
           'scheduled
           nil))))

(defconst *IDemo-heap*
  '((0 . (("java/lang/Class" ("<name>" . "java/lang/Object"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (1 . (("java/lang/Class" ("<name>" . "ARRAY"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (2 . (("java/lang/Class" ("<name>" . "java/lang/Thread"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (3 . (("java/lang/Class" ("<name>" . "java/lang/String"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (4 . (("java/lang/Class" ("<name>" . "java/lang/Class"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
    (5 . (("java/lang/Class" ("<name>" . "IDemo"))
          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))))

(defconst *IDemo-class-table*
  '(("java/lang/Object"
     NIL
     ()
     NIL
     NIL
     (("<init>:()V" NIL
       (RETURN)))
     (REF 0))
    ("ARRAY"
     ("java/lang/Object")
     (("<array>" . *ARRAY*))
     NIL
     NIL
     NIL
     (REF 1))
    ("java/lang/Thread"
     ("java/lang/Object")
     NIL
     NIL
     NIL
     (("run:()V" NIL
       (RETURN))
      ("start:()V" NIL
       ())
      ("stop:()V" NIL
       ())
      ("<init>:()V" NIL
       (ALOAD\_0)
       (INVOKESPECIAL "java/lang/Object" "<init>:()V" 0)
       (RETURN)))
     (REF 2))
    ("java/lang/String"
     ("java/lang/Object")
     ("value:[C")
     NIL
     NIL
     (("<init>:()V" NIL
       (ALOAD\_0)
       (INVOKESPECIAL "java/lang/Object" "<init>:()V" 0)
       (RETURN)))
     (REF 3))
    ("java/lang/Class"
     ("java/lang/Object")
     NIL
     NIL
     NIL
     (("<init>:()V" NIL
       (ALOAD\_0)
       (INVOKESPECIAL "java/lang/Object" "<init>:()V" 0)
       (RETURN)))
     (REF 4))
    ("IDemo"
     ("java/lang/Object")
     NIL
     NIL
     NIL
     (("<init>:()V" NIL
       (ALOAD\_0)
       (INVOKESPECIAL "java/lang/Object" "<init>:()V" 0)
       (RETURN))
      ("ifact:(I)I" NIL
       (ICONST\_1)
       (ISTORE\_1)
       (ICONST\_0)
       (ILOAD\_0)
       (IF\_ICMPGE 14)
       (ILOAD\_0)
       (ILOAD\_1)
       (IMUL)
       (ISTORE\_1)
       (ILOAD\_0)
       (ICONST\_1)
       (ISUB)
       (ISTORE\_0)
       (GOTO -13)
       (ILOAD\_1)
       (IRETURN))
      ("main:([Ljava/lang/String;)V" NIL
       (BIPUSH 8)
       (INVOKESTATIC "IDemo" "ifact:(I)I" 1)
       (POP)
       (RETURN)))
     (REF 5))))

(defconst *IDemo-state*
  (make-state *IDemo-thread-table*
              *IDemo-heap*
              *IDemo-class-table*
              *default-m5-options*))

(defthm idemo-state-is-idemo
  (equal (IDemo)
         *IDemo-state*)
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

; This subroutine computes a schedule suitable for starting at the
; (ICONST_0) at pc 2, which we consider the "top" of the loop.  The
; schedule drives the machine to (but not through) the (IRETURN).

(defun ifact-loop-sched (th n)
  (if (zp n)
      (repeat th 4)
    (append (repeat th 12)
            (ifact-loop-sched th (- n 1)))))

(defun ifact-sched (th n)
  (append (repeat th 3)
          (ifact-loop-sched th n)
          (repeat th 1)))

; Playing Around with Main

; This schedule executes main to termination.

(defun imain-sched (th)
  (append (repeat th 1)
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
  (bound? "ifact:(I)I" (class-decl-methods (bound? "IDemo" *IDemo-class-table*))))

(defun poised-at-ifact-loop (th s n)
  (and (equal (status th s) 'SCHEDULED)
       (equal (pc (top-frame th s)) 2)
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
         (make-frame 2
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
      (class-table s)
      (options s))
     (- n 1))))

(defthm ifact-loop-is-correct
  (implies (poised-at-ifact-loop th s n)
           (equal
            (run (ifact-loop-sched th n) s)
            (modify th s
             :pc 19
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
       (equal (next-inst th s) '(invokestatic "IDemo" "ifact:(I)I" 1))
       (equal n (top (stack (top-frame th s))))
       (intp n)
       (equal (bound? "ifact:(I)I" (class-decl-methods (bound? "IDemo" (class-table s))))
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
