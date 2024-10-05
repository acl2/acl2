; Copyright (C) 2024, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

; Answers to the Problems in :DOC Introduction-to-Apply$

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)

; Problem 1: Assume fn is a binary relation.  Define (insert$ e lst fn) to
; insert e into the list lst in front of the first element, d, in lst such that
; (fn e d) is true.

(defun$ insert$ (e lst fn)
  (cond
   ((endp lst) (cons e lst))
   ((apply$ fn (list e (car lst)))
    (cons e lst))
   (t (cons (car lst) (insert$ e (cdr lst) fn)))))

; Problem 2: Define (sort$ lst fn) to be an insertion sort algorithm for the
; binary relation fn, e.g., to successively insert each element into the
; recursively sorted remaining elements.  (Note: There is no assurance that
; sort$ will actually produce a list ordered by fn because we don't know that
; fn is an ordering relation.)

(defun$ sort$ (lst fn)
  (cond
   ((endp lst) lst)
   (t (insert$ (car lst) (sort$ (cdr lst) fn) fn))))

; Problem 3: Study the four examples below, which illustrate perhaps surprising
; properties of our ``insertion sort'' function.  (If your definitions don't
; have these properties you should back up and redefine your functions as we
; vaguely described above!)

(defthm examples-of-sort$
  (and
   (equal (sort$ '(1 3 -7 0 23) '<)
          '(-7 0 1 3 23))
   (equal (sort$ '(1 3 -7 0 23) (lambda$ (x y) t))
          '(1 3 -7 0 23))
   (equal (sort$ '(1 3 -7 0 23) (lambda$ (x y) nil))
          '(23 0 -7 3 1))
   (equal (sort$ '(1 a 2 x b 3 4 y c) (lambda$ (x y) (symbolp x)))
          '(a x b y c 4 3 2 1)))
  :rule-classes nil)

; Problem 4: Prove the following theorem suggested especially by the last
; example above.  To state this theorem we first introduce the familiar reverse
; function, rev:

(defun rev (x)
  (if (endp x)
      nil
      (append (rev (cdr x))
              (list (car x)))))

; and we use the pre-defined function (when$ fn lst) which computes the
; elements of lst satisfying the unary-function fn, in the order in which they
; occur, e.g., (when$ '(1 a 2 b) 'symbolp) is '(a b).

; Prove:

; (defthm sort$-lambda-symbolp
;   (implies (true-listp lst)
;            (equal (sort$ lst (lambda$ (x y) (symbolp x)))
;                   (append (when$ 'symbolp lst)
;                           (rev (when$ (lambda$ (x y) (not (symbolp x)))
;                                       lst))))))

; Lemmas will be needed.

; Answer to Problem 4:
(defthm true-listp-insert$
  (implies (true-listp lst)
           (true-listp (insert$ e lst fn))))

(defthm insert$-lambda-symbolp
  (implies (true-listp lst)
           (equal (insert$ e lst (lambda$ (x y) (symbolp x)))
                  (if (symbolp e)
                      (cons e lst)
                      (append lst (list e))))))

(defthm sort$-lambda-symbolp
  (implies (true-listp lst)
           (equal (sort$ lst (lambda$ (x y) (symbolp x)))
                  (append (when$ 'symbolp lst)
                          (rev (when$ (lambda$ (x y) (not (symbolp x))) lst))))))

; Problem 5: Define (orderedp$ lst fn) to check whether fn holds between each
; adjacent pair of elements in lst.  Test your function with

; (defthm examples-of-orderedp$
;   (and (orderedp$ '(1 3 5 7) '<)
;        (not (orderedp '(1 3 3 5 7) '<))))

(defun orderedp$ (lst fn)
  (cond ((endp lst) t)
        ((endp (cdr lst)) t)
        (t (and (apply$ fn (list (car lst) (cadr lst)))
                (orderedp$ (cdr lst) fn)))))

(defthm examples-of-orderedp$
  (and (orderedp$ '(1 3 5 7) '<)
       (not (orderedp$ '(1 3 3 5 7) '<)))
  :rule-classes nil)

; Problem 6:  You might hope that 

; (thm (orderedp$ (sort$ lst fn) fn))

; is a theorem.  But it is not as is easily shown by an example.  Try
; (orderedp$ (sort$ '(3 1 5 3 7) '<) '<).  If you look at the output of the
; attempt to prove the thm above you'll see that the proof fails because we do
; not know that (or (fn x y) (fn y x)) is true.  That is, we don't know that fn
; is Strongly Connected.  How could we, since the conjecture is claimed for all
; fn?

; Unfortunately, it is awkward to state that fn is a strongly connected
; relation in ACL2's first-order quantifier free language.  This is a good
; example of the limitations of ACL2's support for second-order functions!

; But we can prove versions of the conjecture for concrete strongly connected
; fns.  The relation named before-dayp, below, is strongly connected, as
; demonstrated by the events following its definition.

; Define

(defun beforep (x y lst)
  (if (and (member x lst)
           (member y lst))
      (member y (member x lst))
      t))

(defun before-dayp (x y)
  (beforep x y '(mon tue wed thu fri sat sun)))

(defthm before-dayp-strongly-connected
  (implies (not (before-dayp x y))
           (before-dayp y x)))

; We disable before-dayp so that it doesn't expand in subsequent proof
; attempts.

(in-theory (disable before-dayp))

; Now, prove the version of (orderedp$ (sort$ lst fn) fn) for the instance when
; fn is 'before-dayp.

; Answer to Problem 6:

(defwarrant before-dayp)

(defthm orderedp$-sort$-before-dayp
  (implies (warrant before-dayp)
           (orderedp$ (sort$ lst 'before-dayp) 'before-dayp)))

