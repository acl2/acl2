; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann, May 2017
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Demo for the talk on ACL2 Workshop 2017 paper
; "A Versatile, Sound Tool for Simplifying Definitions"
; by Alessandro Coglio, Matt Kaufmann, and Eric W. Smith
; See demo-log.txt for a log.

(include-book "simplify-defun")

(defun f1 (x)
  (if (zp x) 0 (+ 1 1 (f1 (+ -1 x)))))
(simplify-defun f1)
:pe f1-becomes-f1{1}
(simplify-defun f1) ; redundant
(simplify-defun
 f1
 :new-name f1-new
 :theorem-name f1-becomes-f1-new
 :theorem-disabled t
 :function-disabled t
 :print-def nil)
:pe f1-new
:pe f1-becomes-f1-new

(defun f2 (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      x ; = nil
    (f2 (cdr x))))
(simplify-defun ; note preservation of (endp x)
 f2
 :assumptions :guard)
:pe f2-becomes-f2{1}

(defun f3 (x y)
  (list (car (cons x x))
        (cdr (cons y y))))
(simplify-defun f3 :simplify-body (list _ @))

(defthm member-equal-revappend
  (iff (member-equal a (revappend x y))
       (or (member-equal a x)
           (member-equal a y))))

(defun f4 (a b x y)
  (let ((a-mem (member-equal a (revappend x y)))
        (b-mem (member-equal b (revappend x y))))
    (and a-mem b-mem)))
(simplify-defun
 f4 ; illustrates equivalences and LET reconstruction
 :theory
 (union-theories '(member-equal-revappend)
                 (theory 'ground-zero)))
(simplify-defun
 f4 ; illustrates equivalences and LET reconstruction
 :new-name f4-new
 :equiv iff
 :theory
 (union-theories '(member-equal-revappend)
                 (theory 'ground-zero)))
:pe f4-becomes-f4-new

