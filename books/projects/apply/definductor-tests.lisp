; Copyright (C) 2020, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Many thanks to ForrestHunt, Inc. for supporting the preponderance of this
; work, and for permission to include it here.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)

; -----------------------------------------------------------------

; Most of our test functions below return 0 and use the loop$ accumulator SUM.
; They were written to develop the nugget idea, which initially only handled
; SUM loop$s.  But z0 is a simple loop$ recursive that uses COLLECT, just to
; test the generalization of the nugget idea.

(defun$ z0 (x)
  (declare (xargs :loop$-recursion t :measure (acl2-count x)))
  (cond ((atom x)
         (if (natp x)
             (if (zp x)
                 0
                 (+ 1 (z0 (- x 1))))
             x))
        ((true-listp x)
         (loop$ for e in x collect (z0 e)))
        (t x)))

(definductor z0)

(defthm z0-thm
  (implies (warrant z0)
           (and (equal (z0 x) x)
                (implies (true-listp x)
                         (equal (loop$ for e in x collect (z0 e)) x))))
  :rule-classes nil)

; -----------------------------------------------------------------
; Fn0

; Features
; (1) recursion both outside and inside a loop$
; (2) case analysis inside the loop$ leading to two kinds of recursions

(defthm acl2-count-unary--
  (implies (integerp x)
           (equal (acl2-count (- x))
                  (acl2-count x))))

(defun$ fn0 (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((natp x)
    (if (equal x 0)
        0
        (fn0 (- x 1))))
   ((true-listp x)
    (loop$ for e in x sum
           (if (and (integerp e) (< e 0))
               (fn0 (- e))
               (fn0 e))))
   (t 0)))

(definductor fn0)

(defthm fn0-thm
  (implies (warrant fn0)
           (and (equal (fn0 x) 0)
                (implies (true-listp x) ; <--- this hyp is optional
                         (equal (loop$ for e in x sum
                                       (if (and (integerp e) (< e 0))
                                           (fn0 (- e))
                                           (fn0 e)))
                                0))))
  :rule-classes nil)

; -----------------------------------------------------------------
; Fn1

; Features:  Like fn0 but the target is cddr'd.  

(defun$ fn1 (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((natp x)
    (if (equal x 0)
        0
        (fn1 (- x 1))))
   ((true-listp x)
    (loop$ for e in (cddr x) sum
           (if (and (integerp e) (< e 0))
               (fn1 (- e))
               (fn1 e))))
   (t 0)))

(definductor fn1)

(defthm fn1-thm
  (implies (warrant fn1)
           (and (equal (fn1 x) 0)
                (implies (true-listp x) ; <--- this hyp is optional
                         (equal (loop$ for e in x sum
                                       (if (and (integerp e) (< e 0))
                                           (fn1 (- e))
                                           (fn1 e)))
                                0))))
  :rule-classes nil)

; -----------------------------------------------------------------
; Fn2
; Features: The simplest nested loop$.

(defun$ fn2 (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((natp x)
    (if (equal x 0)
        0
        (fn2 (- x 1))))
   ((true-listp x)
    (loop$ for e in x sum
           (loop$ for d in e sum (fn2 d))))
   (t 0)))

(definductor fn2)

(defthm fn2-thm
  (implies (warrant fn2 sum$)
    (and (equal (fn2 x) 0)
         (implies (true-listp x) ; <--- this hyp is optional
                  (equal (loop$ for e in x sum
                                (loop$ for d in e sum
                                       (fn2 d)))
                         0))
         (equal (loop$ for d in x sum
                       (fn2 d))
                0)))
  :rule-classes nil)

; -----------------------------------------------------------------
; Fn3
; Features:  a nested loop where the inner target is cddr'd

(defun$ fn3 (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((natp x)
    (if (equal x 0)
        0
        (fn3 (- x 1))))
   ((true-listp x)
    (loop$ for e in x sum
           (loop$ for d in (cddr e) sum (fn3 d))))
   (t 0)))

(definductor fn3)

(defthm fn3-thm
  (implies (warrant fn3 sum$)
           (and (equal (fn3 x) 0)
                (equal (loop$ for e in x sum
                              (loop$ for d in (cddr e) sum
                                     (fn3 d)))
                       0)
                (equal (loop$ for d in x sum
                              (fn3 d))
                       0)
                ))
  :rule-classes nil)


; -----------------------------------------------------------------
; Fn4
; Features: A nested loop with cddr, interior cases, and more recursions.

(defun$ fn4 (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((natp x)
    (if (equal x 0)
        0
        (fn4 (- x 1))))
   ((true-listp x)
    (loop$ for e in x sum
           (+ (fn4 e)
              (loop$ for d in (cddr e) sum
                     (if (and (integerp d) (< d 0))
                         (fn4 (- d))
                         (fn4 d))))))
   (t 0)))

(definductor fn4)

(defthm fn4-thm
  (implies (warrant fn4 sum$)
    (and (equal (fn4 x) 0)
         (equal (loop$ for e in x sum
                       (+ (fn4 e)
                          (loop$ for d in (cddr e) sum
                                 (if (and (integerp d) (< d 0))
                                     (fn4 (- d))
                                     (fn4 d)))))
                0)
         (equal (loop$ for d in x sum
                       (if (and (integerp d) (< d 0))
                           (fn4 (- d))
                           (fn4 d)))
                0)))
  :rule-classes nil)
; Time:  4.21 seconds (prove: 4.19, print: 0.02, other: 0.00)
; -----------------------------------------------------------------
; Fn5
; Features: Tripply nested loops with cddr and caar

(defun$ fn5 (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((natp x)
    (if (equal x 0)
        0
        (fn5 (- x 1))))
   ((true-listp x)
    (loop$ for e in x sum
           (+ (fn5 e)
              (loop$ for c in (cddr e) sum
                     (loop$ for d in (cddr c) sum
                            (if (and (integerp d) (< d 0))
                                (fn5 (- d))
                                (fn5 d)))))))
   (t 0)))

(definductor fn5)

(defthm fn5-thm
  (implies (warrant fn5 sum$)
    (and (equal (fn5 x) 0)
         (equal (loop$ for e in x sum
                       (+ (fn5 e)
                          (loop$ for c in (cddr e) sum
                                 (loop$ for d in (cddr c) sum
                                        (if (and (integerp d) (< d 0))
                                            (fn5 (- d))
                                            (fn5 d))))))
                0)
         (equal (loop$ for c in x sum
                       (loop$ for d in (cddr c) sum
                              (if (and (integerp d) (< d 0))
                                  (fn5 (- d))
                                  (fn5 d))))
                0)
         (equal (loop$ for d in x sum
                       (if (and (integerp d) (< d 0))
                           (fn5 (- d))
                           (fn5 d)))
                0)))
  :rule-classes nil)

;-----------------------------------------------------------------
; z1
; Features: Extra formals.  However, to prevent fn6 from using fancy scions the
; extra actuals in loop$ recursive calls are constants!

(defun$ z1 (a x b)
  (declare (xargs :loop$-recursion t :measure (acl2-count x)))
  (cond ((atom x)
         (if (natp x)
             (if (zp x)
                 0
                 (+ 1 (z1 (+ 1 a) (- x 1) (* 2 b))))
             x))
        ((true-listp x)
         (loop$ for e in x collect (z1 0 e 1)))
        (t (* (+ a b) x))))

(definductor z1)

(defthm z1-thm
  (implies (warrant z1)
           (and (implies (natp x) (equal (z1 a x c) x))
                (implies (nat-listp x)
                         (equal (loop$ for e in x collect (z1 0 e 1)) x))))
  :rule-classes nil)

;-----------------------------------------------------------------
; Fn6
; Features: Our first fancy loop$.

(defun$ fn6 (x c)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((natp x)
    (if (equal x 0)
        c
        (fn6 (- x 1) c)))
   ((true-listp x)
    (loop$ for e in x sum
           (if (and (integerp e) (< e 0))
               (fn6 (- e) c)
               (fn6 e c))))
   (t c)))

(definductor fn6)

(defthm fn6-thm
  (implies (warrant fn6)
           (and (implies (natp x) (equal (fn6 x 0) 0))
                (implies (nat-listp x)
                         (equal (loop$ for e in x sum (fn6 e 0)) 0))))
  :rule-classes nil)

;-----------------------------------------------------------------
; Fn7
; Features: Simultaneous sweep over two vars.

(defun$ fn7 (x c y)
  (declare (xargs :loop$-recursion t
                  :measure (+ (acl2-count x)
                              (acl2-count y))))
  (cond
   ((natp x)
    (if (equal x 0)
        c
        (fn7 (- x 1) c y)))
   ((natp y)
    (if (equal y 0)
        c
        (fn7 x c (- y 1))))
   (t (loop$ for e in x as d in y
             sum
             (cond ((and (consp e)
                         (consp d))
                    (fn7 e c d))
                   (t c))))))

(definductor fn7)

(defthm fn7-thm
  (implies (warrant fn7)
           (and (implies (natp x) (equal (fn7 x 0 y) 0))
                (implies (natp y) (equal (fn7 x 0 y) 0))
                (implies (equal c 0)
                         (equal (loop$ for e in x as d in y
                                       sum
                                       (cond ((and (consp e)
                                                   (consp d))
                                              (fn7 e c d))
                                             (t c)))
                                0))))
  :rule-classes nil)

; -----------------------------------------------------------------
; Z2
; Feature: Relating a loop$ recursive function to a mutually recursive one.

; This function returns 0 but is sort of an extreme simplification of
; pseudo-termp-type recursion.

(defun$ z2 (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond ((atom x)
         0)
        (t (loop$ for e in (cdr x) sum (z2 e)))))

(definductor z2)

(defthm z2-thm
  (implies (warrant z2)
           (and (equal (z2 x) 0)
                (equal (loop$ for e in x sum (z2 e)) 0)))
  :rule-classes nil)

(mutual-recursion

 (defun mr-z2 (x)
   (declare (xargs :measure (acl2-count x)))
   (if (atom x)
       0
       (mr-z2-list (cdr x))))
 (defun mr-z2-list (x)
   (declare (xargs :measure (acl2-count x)))
   (if (endp x)
       0
       (+ (fix (mr-z2 (car x)))
          (mr-z2-list (cdr x)))))
 )

(defthm mr-z2-is-z2
  (implies (warrant z2)
           (and (equal (z2 x) (mr-z2 x))
                (equal (loop$ for e in x sum (z2 e))
                       (mr-z2-list x))))
  :rule-classes nil)

; -----------------------------------------------------------------
; Copy-nat-tree
; Features: a little closer to pseudo-termp and exploring mutual recursion

(defun$ nat-treep (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((atom x) (natp x))
   (t (and (true-listp x)
           (eq (car x) 'NATS)
           (loop$ for e in (cdr x) always (nat-treep e))))))

(defthm examples-of-nat-treep
  (implies
   (warrant nat-treep)
   (and (equal (nat-treep '(nats
                            (nats 1 2 3)
                            4
                            (nats 5 (nats 6 7 8) 9))) t)
        (equal (nat-treep '(nats (nats 1 2 3) bad)) nil)))
  :rule-classes nil)

(definductor nat-treep)

(defun$ copy-nat-tree (x)
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond
   ((atom x)
    (if (natp x)
        (if (equal x 0)
            0
            (+ 1 (copy-nat-tree (- x 1))))
        x))
   (t (cons 'nats
            (loop$ for e in (cdr x) collect (copy-nat-tree e))))))

(definductor copy-nat-tree)

(defthm copy-nat-tree-copies
  (implies (warrant nat-treep copy-nat-tree)
           (and (implies (nat-treep x) (equal (copy-nat-tree x) x))
                (implies (and (true-listp x)
                              (loop$ for e in x always (nat-treep e)))
                         (equal (loop$ for e in x collect (copy-nat-tree e))
                                x))))
  :rule-classes nil)

(mutual-recursion
 (defun mr-copy-nat-tree (x)
   (cond
    ((atom x)
     (if (natp x)
         (if (equal x 0)
             0
             (+ 1 (mr-copy-nat-tree (- x 1))))
         x))
    (t (cons 'nats
             (mr-copy-nat-tree-list (cdr x))))))

 (defun mr-copy-nat-tree-list (x)
   (cond
    ((endp x) nil)
    (t (cons (mr-copy-nat-tree (car x))
             (mr-copy-nat-tree-list (cdr x)))))))

(defthm mr-copy-nat-tree-copies
  (implies (warrant nat-treep)
           (and (implies (nat-treep x)
                         (equal (mr-copy-nat-tree x) x))
                (implies (and (true-listp x)
                              (loop$ for e in x always (nat-treep e)))
                         (equal (mr-copy-nat-tree-list x) x))))
  :hints (("Goal" :induct (copy-nat-tree x)))
  :rule-classes nil)

(defthm copy-nat-tree-is-mr-copy-nat-tree
  (implies (warrant nat-treep copy-nat-tree)
           (and (implies (nat-treep x)
                         (equal (copy-nat-tree x)
                                (mr-copy-nat-tree x)))
                (implies (and (true-listp x)
                              (loop$ for e in x always (nat-treep e)))
                         (equal (loop$ for e in x collect (copy-nat-tree e))
                                (mr-copy-nat-tree-list x)))))
  :rule-classes nil)

; -----------------------------------------------------------------
; Pstermp

; Features: trying the methodology above.

(defun$ pstermp (x)
; This is the ACL2 built-in pseudo-termp, expressed with loop$
  (declare (xargs :loop$-recursion t
                  :measure (acl2-count x)))
  (cond ((atom x) (symbolp x))
        ((eq (car x) 'quote)
         (and (consp (cdr x))
              (null (cdr (cdr x)))))
        ((not (true-listp x)) nil)
        ((loop$ for e in (cdr x) always (pstermp e))
         (or (symbolp (car x))
             (and (true-listp (car x))
                  (equal (length (car x)) 3)
                  (eq (car (car x)) 'lambda)
                  (symbol-listp (cadr (car x)))
                  (pstermp (caddr (car x)))
                  (equal (length (cadr (car x)))
                         (length (cdr x))))))
        (t nil)))

(definductor pstermp)

(defthm always$-t
  (equal (always$ '(lambda (e) 't) x) t))

(defthm pstermp-is-pseudo-termp
   (implies (warrant pstermp)
            (and (equal (pstermp x) (pseudo-termp x))
                 (equal (and (true-listp x)
                             (loop$ for e in x always (pstermp e)))
                        (pseudo-term-listp x))))
   :rule-classes nil)

