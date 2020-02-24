; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Formalization in ACL2 of the template functions, theorems, and proofs
; in the design notes, for n = p = 1.

(must-succeed*

 (encapsulate

   ;; guarded functions:

   (((f *) => * :formals (x) :guard (gamma-f x))
    ((c1 *) => * :formals (x) :guard (gamma-c1 x))
    ((h0 *) => *)
    ((h1 *) => *)
    ((f0 *) => * :formals (x) :guard (gamma-f0 x))
    ((f1 *) => * :formals (x) :guard (gamma-f1 x))
    ((gamma-f *) => *)
    ((gamma-c1 *) => *)
    ((gamma-f0 *) => *)
    ((gamma-f1 *) => *))

   (local (defun f (x) x))
   (local (defun c1 (x) (declare (ignore x)) t))
   (local (defun h0 (x) (declare (ignore x)) t))
   (local (defun h1 (x) (declare (ignore x)) t))
   (local (defun f0 (x) x))
   (local (defun f1 (x) x))
   (local (defun gamma-f (x) (declare (ignore x)) t))
   (local (defun gamma-c1 (x) (declare (ignore x)) t))
   (local (defun gamma-f0 (x) (declare (ignore x)) t))
   (local (defun gamma-f1 (x) (declare (ignore x)) t))

   ;; existing theorems:

   (defthm f-f1
     (implies (h1 x)
              (equal (f x) (f1 x)))
     :rule-classes nil)

   (defthm f-f0
     (implies (h0 x)
              (equal (f x) (f0 x)))
     :rule-classes nil)

   ;; applicability conditions;

   (defthm hh1
     (implies (c1 x)
              (h1 x))
     :rule-classes nil)

   (defthm hh0
     (implies (not (c1 x))
              (h0 x))
     :rule-classes nil)

   (defthm gc1
     (implies (gamma-f x)
              (gamma-c1 x))
     :rule-classes nil)

   (defthm gf1
     (implies (and (gamma-f x)
                   (c1 x))
              (gamma-f1 x))
     :rule-classes nil)

   (defthm gf0
     (implies (and (gamma-f x)
                   (not (c1 x)))
              (gamma-f0 x))
     :rule-classes nil)) ; end of ENCAPSULATE

 ;; generated function and theorem:

 (defund fprime (x)
   (declare (xargs :guard (gamma-f x)
                   :guard-hints (("Goal"
                                  :in-theory nil
                                  :use (gc1 gf1 gf0)))))
   (cond ((c1 x) (f1 x))
         (t (f0 x))))

 (defthm f-fprime
   (equal (f x) (fprime x))
   :hints (("Goal"
            :in-theory '(fprime)
            :use (f-f1 f-f0 hh1 hh0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Formalization in ACL2 of the template functions, theorems, and proofs
; in the design notes, for n = 2 and p = 3.

(must-succeed*

 (encapsulate

   ;; guarded functions:

   (((f * *) => * :formals (x y) :guard (gamma-f x y))
    ((c1 * *) => * :formals (x y) :guard (gamma-c1 x y))
    ((c2 * *) => * :formals (x y) :guard (gamma-c2 x y))
    ((c3 * *) => * :formals (x y) :guard (gamma-c3 x y))
    ((h0 * *) => *)
    ((h1 * *) => *)
    ((h2 * *) => *)
    ((h3 * *) => *)
    ((f0 * *) => * :formals (x y) :guard (gamma-f0 x y))
    ((f1 * *) => * :formals (x y) :guard (gamma-f1 x y))
    ((f2 * *) => * :formals (x y) :guard (gamma-f2 x y))
    ((f3 * *) => * :formals (x y) :guard (gamma-f3 x y))
    ((gamma-f * *) => *)
    ((gamma-c1 * *) => *)
    ((gamma-c2 * *) => *)
    ((gamma-c3 * *) => *)
    ((gamma-f0 * *) => *)
    ((gamma-f1 * *) => *)
    ((gamma-f2 * *) => *)
    ((gamma-f3 * *) => *))

   (local (defun f (x y) (cons x y)))
   (local (defun c1 (x y) (declare (ignore x y)) t))
   (local (defun c2 (x y) (declare (ignore x y)) t))
   (local (defun c3 (x y) (declare (ignore x y)) t))
   (local (defun h0 (x y) (declare (ignore x y)) t))
   (local (defun h1 (x y) (declare (ignore x y)) t))
   (local (defun h2 (x y) (declare (ignore x y)) t))
   (local (defun h3 (x y) (declare (ignore x y)) t))
   (local (defun f0 (x y) (cons x y)))
   (local (defun f1 (x y) (cons x y)))
   (local (defun f2 (x y) (cons x y)))
   (local (defun f3 (x y) (cons x y)))
   (local (defun gamma-f (x y) (declare (ignore x y)) t))
   (local (defun gamma-c1 (x y) (declare (ignore x y)) t))
   (local (defun gamma-c2 (x y) (declare (ignore x y)) t))
   (local (defun gamma-c3 (x y) (declare (ignore x y)) t))
   (local (defun gamma-f0 (x y) (declare (ignore x y)) t))
   (local (defun gamma-f1 (x y) (declare (ignore x y)) t))
   (local (defun gamma-f2 (x y) (declare (ignore x y)) t))
   (local (defun gamma-f3 (x y) (declare (ignore x y)) t))

   ;; existing theorems:

   (defthm f-f1
     (implies (h1 x y)
              (equal (f x y) (f1 x y)))
     :rule-classes nil)

   (defthm f-f2
     (implies (h2 x y)
              (equal (f x y) (f2 x y)))
     :rule-classes nil)

   (defthm f-f3
     (implies (h3 x y)
              (equal (f x y) (f3 x y)))
     :rule-classes nil)

   (defthm f-f0
     (implies (h0 x y)
              (equal (f x y) (f0 x y)))
     :rule-classes nil)

   ;; applicability conditions;

   (defthm hh1
     (implies (c1 x y)
              (h1 x y))
     :rule-classes nil)

   (defthm hh2
     (implies (and (not (c1 x y))
                   (c2 x y))
              (h2 x y))
     :rule-classes nil)

   (defthm hh3
     (implies (and (not (c1 x y))
                   (not (c2 x y))
                   (c3 x y))
              (h3 x y))
     :rule-classes nil)

   (defthm hh0
     (implies (and (not (c1 x y))
                   (not (c2 x y))
                   (not (c3 x y)))
              (h0 x y))
     :rule-classes nil)

   (defthm gc1
     (implies (gamma-f x y)
              (gamma-c1 x y))
     :rule-classes nil)

   (defthm gc2
     (implies (and (gamma-f x y)
                   (not (c1 x y)))
              (gamma-c2 x y))
     :rule-classes nil)

   (defthm gc3
     (implies (and (gamma-f x y)
                   (not (c1 x y))
                   (not (c2 x y)))
              (gamma-c3 x y))
     :rule-classes nil)

   (defthm gf1
     (implies (and (gamma-f x y)
                   (c1 x y))
              (gamma-f1 x y))
     :rule-classes nil)

   (defthm gf2
     (implies (and (gamma-f x y)
                   (not (c1 x y))
                   (c2 x y))
              (gamma-f2 x y))
     :rule-classes nil)

   (defthm gf3
     (implies (and (gamma-f x y)
                   (not (c1 x y))
                   (not (c2 x y))
                   (c3 x y))
              (gamma-f3 x y))
     :rule-classes nil)

   (defthm gf0
     (implies (and (gamma-f x y)
                   (not (c1 x y))
                   (not (c2 x y))
                   (not (c3 x y)))
              (gamma-f0 x y))
     :rule-classes nil)) ; end of ENCAPSULATE

 ;; generated function and theorem:

 (defund fprime (x y)
   (declare (xargs :guard (gamma-f x y)
                   :guard-hints (("Goal"
                                  :in-theory nil
                                  :use (gc1 gc2 gc3 gf1 gf2 gf3 gf0)))))
   (cond ((c1 x y) (f1 x y))
         ((c2 x y) (f2 x y))
         ((c3 x y) (f3 x y))
         (t (f0 x y))))

 (defthm f-fprime
   (equal (f x y) (fprime x y))
   :hints (("Goal"
            :in-theory '(fprime)
            :use (f-f1 f-f2 f-f3 f-f0 hh1 hh2 hh3 hh0)))))
