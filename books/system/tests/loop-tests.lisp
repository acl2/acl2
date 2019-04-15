; Copyright (C) 2019, Regents of the University of Texas
; Written by J Moore with contributions from Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)

; The Little Test - Code7 passes Little Test
(defun$ rsq (x)(declare (xargs :guard (rationalp x))) (* x x))
(defun$ isq (x)(declare (xargs :guard (integerp x))) (* x x))
(defun$ symp (x) (declare (xargs :guard t))
  (if (equal x 23)
      nil
      (symbolp x)))
(defun$ ssq (x)
  (declare (xargs :guard (symp x)))
  (length (symbol-name x)))

; This fails because of the lack of a :guard clause and the lack of
; warrants:
; (defun foo (ilst xlst c) ; will fail!
;   (declare (xargs :guard (and (integer-listp ilst)
;                               (rational-listp xlst)
;                               (symbolp c))))
;   (loop$ for i of-type integer in ilst
;          as  x of-type rational in xlst
;          sum (+ (isq i) (rsq x) (ssq c))))

(defun foo (ilst xlst c)
  (declare (xargs :guard (and (warrant isq rsq ssq)
                              (integer-listp ilst)
                              (rational-listp xlst)
                              (symbolp c))))
  (loop$ for i of-type integer in ilst
         as  x of-type rational in xlst
         sum :guard (symp c) (+ (isq i) (rsq x) (ssq c))))


; The Big Test -- Code7 passes the Big Test
(defun test (n)

; Best to call this with (<= 10 n) to expect every until/when to have some effect.

  (declare (xargs :guard (natp n)
                  :verify-guards nil))
  (list
; SUM
; simple (in/on/from-to-by)
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          sum x)
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          sum (length x))
   (loop$ for x of-type integer from 1 to n sum x)
; ... with until
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          until (equal x 7)
          sum x)
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 7)
          sum (length x))
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 8)
          sum x)
; ... with when
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          when (not (equal x 7))
          sum x)
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          when (not (equal (car x) 7))
          sum (length x))
   (loop$ for x of-type integer
          from 1 to n
          when (not (equal x 7))
          sum x)
; ... with until and when
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal x 7))
          sum x)
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 9)
          when (not (equal (car x) 7))
          sum (length x))
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 9)
          when (not (equal x 7))
          sum x)

; ALWAYS
; simple (in/on/from-to-by)
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          always (integerp x))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          always (true-listp x))
   (loop$ for x of-type integer from 1 to n always (integerp x))
; ... with until
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          until (equal x 7)
          always (integerp x))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 7)
          always (true-listp x))
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 8)
          always (integerp x))
; ... with when -- illegal with always
; ... with until and when -- illegal with always

; COLLECT
; simple (in/on/from-to-by)
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          collect x)
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          collect (length x))
   (loop$ for x of-type integer from 1 to n collect x)
; ... with until
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          until (equal x 7)
          collect x)
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 7)
          collect (length x))
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 8)
          collect x)
; ... with when
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          when (not (equal x 7))
          collect x)
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          when (not (equal (car x) 7))
          collect (length x))
   (loop$ for x of-type integer
          from 1 to n
          when (not (equal x 7))
          collect x)
; ... with until and when
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal x 7))
          collect x)
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 9)
          when (not (equal (car x) 7))
          collect (length x))
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 9)
          when (not (equal x 7))
          collect x)

; APPEND
; simple (in/on/from-to-by)
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          append (list x))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          append x)
   (loop$ for x of-type integer from 1 to n append (list x))
; ... with until
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          until (equal x 7)
          append (list x))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 7)
          append x)
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 8)
          append (list x))
; ... with when
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          when (not (equal x 7))
          append (list x))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          when (not (equal (car x) 7))
          append x)
   (loop$ for x of-type integer
          from 1 to n
          when (not (equal x 7))
          append (list x))
; ... with until and when
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal x 7))
          append (list x))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 9)
          when (not (equal (car x) 7))
          append x)
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 9)
          when (not (equal x 7))
          append (list x))

; -----------------------------------------------------------------
; And now we'll repeat all of that with an AS clause

; SUM
; simple (in/on/from-to-by)
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          sum :guard (symbolp sym) (+ x (length (symbol-name sym))))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          sum :guard (symbolp sym) (+ (length x) (length (symbol-name sym))))

   (loop$ for x of-type integer from 1 to n
          as sym in '(a b c d e f g h i j k l m n o p)
          sum :guard (symbolp sym) (+ x (length (symbol-name sym))))

; ... with until
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          until :guard (symp sym) (or (equal x 7) (eq sym '(a b c)))
          sum :guard (symp sym) (+ x (length (symbol-name sym))))

   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 7)
          sum (length x))
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 8)
          sum x)

; ... with when
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as rattail of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/2)
          when (and (<= x 6) rattail (<= (car rattail) 7))
          sum (+ x (length rattail)))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          as rattail of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/2)
          when (and (<= (length x) 6) rattail (<= (car rattail) 7))
          sum :guard rattail (+ (length x) (car rattail)))
   (loop$ for x of-type integer
          from 1 to n
          as rattail of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/2)
          when (and (<= x 6) rattail (<= (car rattail) 7))
          sum :guard rattail (+ x (car rattail)))

; ... with until and when
   (loop$ for x of-type integer in (make-list n :initial-element 1)
          as y of-type rational in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal y 7))
          sum x)
   (loop$ for x of-type (satisfies rational-listp)
              on (make-list n :initial-element 1)
          as
          y of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/3)
          until :guard x (equal (car x) 9)
          when :guard x (not (equal (car x) 1/3))
          sum :guard y (+ (length x) (car y)))
   (loop$ for x of-type integer from 1 to n
          as y of-type rational in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal y 7))
          sum x)

; ALWAYS
; simple (in/on/from-to-by)
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          always :guard (symbolp sym) (< (+ x (length (symbol-name sym))) 100))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          always :guard (symbolp sym) (< (+ (length x) (length (symbol-name sym))) 100))

   (loop$ for x of-type integer from 1 to n
          as sym in '(a b c d e f g h i j k l m n o p)
          always :guard (symbolp sym) (< (+ x (length (symbol-name sym))) 100))

; ... with until
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          until :guard (symp sym) (or (equal x 7) (eq sym '(a b c)))
          always :guard (symp sym) (< (+ x (length (symbol-name sym))) 100))

   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 7)
          always (< (length x) 100))
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 8)
          always (< x 100))

; ... with when -- illegal with always
; ... with until and when -- illegal with always

; COLLECT
; simple (in/on/from-to-by)
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          collect :guard (symbolp sym) (+ x (length (symbol-name sym))))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          collect :guard (symbolp sym) (+ (length x) (length (symbol-name sym))))

   (loop$ for x of-type integer from 1 to n
          as sym in '(a b c d e f g h i j k l m n o p)
          collect :guard (symbolp sym) (+ x (length (symbol-name sym))))

; ... with until
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          until :guard (symp sym) (or (equal x 7) (eq sym '(a b c)))
          collect :guard (symp sym) (+ x (length (symbol-name sym))))

   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 7)
          collect (length x))
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 8)
          collect x)

; ... with when
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as rattail of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/2)
          when (and (<= x 6) rattail (<= (car rattail) 7))
          collect (+ x (length rattail)))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          as rattail of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/2)
          when (and (<= (length x) 6) rattail (<= (car rattail) 7))
          collect :guard rattail (+ (length x) (car rattail)))
   (loop$ for x of-type integer
          from 1 to n
          as rattail of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/2)
          when (and (<= x 6) rattail (<= (car rattail) 7))
          collect :guard rattail (+ x (car rattail)))

; ... with until and when
   (loop$ for x of-type integer in (make-list n :initial-element 1)
          as y of-type rational in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal y 7))
          collect x)
   (loop$ for x of-type (satisfies rational-listp)
              on (make-list n :initial-element 1)
          as
          y of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/3)
          until :guard x (equal (car x) 9)
          when :guard x (not (equal (car x) 1/3))
          collect :guard y (+ (length x) (car y)))
   (loop$ for x of-type integer from 1 to n
          as y of-type rational in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal y 7))
          collect x)


; APPEND
; simple (in/on/from-to-by)
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          append :guard (symbolp sym) (make-list-ac 3 (+ x (length (symbol-name sym))) nil))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          append :guard (symbolp sym) (make-list-ac 3 (+ (length x) (length (symbol-name sym))) nil))

   (loop$ for x of-type integer from 1 to n
          as sym in '(a b c d e f g h i j k l m n o p)
          append :guard (symbolp sym) (make-list-ac 3 (+ x (length (symbol-name sym))) nil))

; ... with until
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as sym in '(a b c d e f g h i j k l m n o p)
          until :guard (symp sym) (or (equal x 7) (eq sym '(a b c)))
          append :guard (symp sym) (make-list-ac 3 (+ x (length (symbol-name sym))) nil))

   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          until (equal (car x) 7)
          append x)
   (loop$ for x of-type integer
          from 1 to n
          until (equal x 8)
          append (list x))

; ... with when
   (loop$ for x of-type integer
          in (make-list n :initial-element 1)
          as rattail of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/2)
          when (and (<= x 6) rattail (<= (car rattail) 7))
          append (cons x rattail))
   (loop$ for x of-type (satisfies true-listp)
          on (make-list n :initial-element 1)
          as rattail of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/2)
          when (and (<= (length x) 6) rattail (<= (car rattail) 7))
          append (append x rattail))
   (loop$ for x of-type integer
          from 1 to n
          as rattail of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/2)
          when (and (<= x 6) rattail (<= (car rattail) 7))
          append (cons x rattail))

; ... with until and when
   (loop$ for x of-type integer in (make-list n :initial-element 1)
          as y of-type rational in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal y 7))
          append (list x))
   (loop$ for x of-type (satisfies rational-listp)
              on (make-list n :initial-element 1)
          as
          y of-type (satisfies rational-listp)
             on (make-list n :initial-element 1/3)
          until :guard x (equal (car x) 9)
          when :guard x (not (equal (car x) 1/3))
          append (append x y))
   (loop$ for x of-type integer from 1 to n
          as y of-type rational in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal y 7))
          append (list x y))

; And finally, a global variable

   (loop$ for x of-type integer from 1 to n
          as y of-type rational in (make-list n :initial-element 1)
          until (equal x 9)
          when (not (equal y 7))
          append :guard (rationalp n) (list x y (+ 1 n)))

   ))

(make-event
 `(defconst *test-15-a*
    ',(test 15)))

(verify-guards test
  :hints
  (("Goal" :in-theory (disable loop$-as) ; <---- This is important! ***
    :do-not-induct t)))

(make-event
 `(defconst *test-15-b*
    ',(test 15)))

(assert-event (equal *test-15-a* *test-15-b*))

; -----------------------------------------------------------------
; The Boohoo Problem

; Consider the following defun in a world in which we don't know
; true-listp-append-rewrite or the earlier mentioned boohoo-lemma.

; The following will fail.

(include-book "misc/eval" :dir :system)

(must-fail
(defun boohoo (n)
  (declare (xargs :guard (natp n)
                  :guard-hints (("Goal"
                                 :in-theory
                                 (disable loop$-as
                                          true-listp-append-rewrite) ; <--- ****
                                 :do-not-induct t))))
  (loop$ for x of-type (satisfies true-listp)
         on (make-list n :initial-element 1)
         as rattail of-type (satisfies rational-listp)
         on (make-list n :initial-element 1/2)
         when (and (<= (length x) 6) rattail (<= (car rattail) 7))
         append (append x rattail))))

; Note that x is known to satisfy true-listp and rattail satisfies rational-listp.
; The special guard on the append loop$ op is true-listp.  So in one sense
; it would seem sufficient if we could prove

; (thm (implies (and (true-listp a)
;                    (rational-listp b))
;               (true-listp (append a b))))

; which in fact we can.  But the guard verification of boohoo fails with the
; following checkpoint.

(thm
 (IMPLIES (AND (INTEGERP N)
               (<= 0 N)
               (MEMBER-EQUAL NEWV
                             (LOOP$-AS (LIST (TAILS (MAKE-LIST-AC N 1 NIL))
                                             (TAILS (MAKE-LIST-AC N 1/2 NIL)))))
               (NOT (STRINGP (CAR NEWV)))
               (<= (LEN (CAR NEWV)) 6)
               (CADR NEWV)
               (<= (CAR (CADR NEWV)) 7))
          (TRUE-LISTP (APPEND (CAR NEWV) (CADR NEWV)))))

; To prove this with our machinery we need to rely on fancy-uqi-true-list-2.
; All the uqi rules target the (member-equal ...) and contain the negation of
; the type property of the appropriate element of newv as a hyp.  In the case
; of fancy-uqi-true-list-2 the relevant hyp is

; (not (true-listp (cadr newv)))

; We expect to relieve this hyp of fancy-uqi-true-list-2 using the negation of
; of the guard conjecture conclusion, which in this case is:

; (not (TRUE-LISTP (APPEND (CAR NEWV) (CADR NEWV))))

; So either we need to have rewritten that concl as per
; true-listp-append-rewrite, or we need

(defthm boohoo-lemma
  (implies (not (true-listp (append a b)))
           (not (true-listp b))))

; With boohoo lemma, for example, (defun boohoo ...) succeeds.

(defun boohoo (n)
  (declare (xargs :guard (natp n)
                  :guard-hints (("Goal"
                                 :in-theory
                                 (disable loop$-as
                                          true-listp-append-rewrite) ; <--- ****
                                 :do-not-induct t))))
  (loop$ for x of-type (satisfies true-listp)
         on (make-list n :initial-element 1)
         as rattail of-type (satisfies rational-listp)
         on (make-list n :initial-element 1/2)
         when (and (<= (length x) 6) rattail (<= (car rattail) 7))
         append (append x rattail)))

; The moral is that our lemma machine is ok for proving the guards on the
; components of LOCALS but lousy for proving the guards on the output of the
; body.

; Here is a little example that illustrates the need to make code executable in
; the loop$-alist (with a process that we used to call "twoify" and now
; call "logic-code-to-runnable-code").

(defun$ my-mv (x)
  (declare (xargs :guard t))
  (mv x x))

(defun loop-with-my-mv-target ()
  (declare (xargs :verify-guards t))
  (loop$ for x in (mv-let (a b)
                    (my-mv '(1 2 3))
                    (append a b))
         collect x))

(thm (equal (loop-with-my-mv-target) '(1 2 3 1 2 3)))

; The following example used to succeed because we evaluated away the ground
; loop$ and did not generate Special Conjectures.  But then when we evaluated
; (bug1) in ACL2 it caused a hard error in raw Lisp if running CCL with

; (declaim (optimize (safety 3)))

; because not every member of the target is below 3!

(defun below-3p (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 3)))

(must-fail
 (defun bug1 ()
   (declare (xargs :guard t))
   (loop$ for x of-type (satisfies below-3p) in '(1 2 3 4 5) collect x)))

; This example used to succeed before because we did not realize that we needed
; Special Conjecture (c).  After the guard verified bug2 was admitted, (bug2
; '(1 2 3)) caused a hard error because NIL is a tail of '(1 2 3).  CCL tests
; the type-spec on every tail of the target of an ON-iteration, not just the
; non-empty tails!  If this example succeeds, it indicates that we are failing
; to generate Special Conjecture (c).

(must-fail
 (defun bug2 (lst)
   (declare (xargs :guard (integer-listp lst)))
   (loop$ for x of-type (and (satisfies integer-listp) (not (satisfies null)))
          on lst
	  collect x)))

; This example used to succeed because we thought from-to-by iteration stayed
; within the obvious bounds and didn't test the type-spec on the first value of
; the iteration variable strictly larger than the max, i.e., on (+ i k (* k
; (floor (- j i) k))), for (from-to-by i j k).  After mistakenly guard
; verifying bug3, (bug3) caused a hard error on 13.

(defun below-11p (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 11)))

(must-fail
 (defun bug3 ()
   (declare (xargs :guard t))
   (loop$ for i of-type (satisfies below-11p) from 1 to 10 by 3
          collect i)))

; -----------------------------------------------------------------
; Relaxing translate
; These tests failed until we relaxed the translation of loop$ for theorems.

(thm
 (equal (loop$ for x in '(1 2) collect (mv x x))
        '((1 1) (2 2))))

(defun-nx loop-test-1-using-my-mv ()
  (loop$ for x in '(1 2) collect (my-mv x)))

(defun loop-test-2-using-my-mv ()
  (non-exec (loop$ for x in '(1 2) collect (mv x x))))

(must-fail ; Loop$ translation is not relaxed inside function bodies.
 (defun bad (lst)
   (declare (xargs :guard (true-listp lst)))
   (loop$ for x in lst collect (car (my-mv x)))))

(thm ; Succeeds, but note that we run collect$, not a raw Lisp loop.
 (implies (warrant my-mv)
          (equal (loop$ for x in '(1 2 3) collect (car (my-mv x)))
                 '(1 2 3))))
