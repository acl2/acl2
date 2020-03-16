; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "casesplit")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-verify-guards-eagerness 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-title (str)
  `(cw-event (concatenate 'string "~%~%~%********** " ,str "~%~%")))

(defmacro casesplit (&rest args)
  `(apt::casesplit ,@args))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test template for n = p = 1.")

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
              (equal (f x) (f1 x))))

   (defthm f-f0
     (implies (h0 x)
              (equal (f x) (f0 x))))

   ;; applicability conditions;

   (defthm hh1
     (implies (c1 x)
              (h1 x)))

   (defthm hh0
     (implies (not (c1 x))
              (h0 x)))

   (defthm gc1
     (implies (gamma-f x)
              (gamma-c1 x)))

   (defthm gf1
     (implies (and (gamma-f x)
                   (c1 x))
              (gamma-f1 x)))

   (defthm gf0
     (implies (and (gamma-f x)
                   (not (c1 x)))
              (gamma-f0 x)))) ; end of ENCAPSULATE

 (casesplit f ((c1 x)) (f-f1 f-f0))

 (assert! (function-namep 'f{1} (w state)))

 (assert! (theorem-namep 'f-~>-f{1} (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Test template for n = 2 and p = 2.")

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
              (h1 x y)))

   (defthm hh2
     (implies (and (not (c1 x y))
                   (c2 x y))
              (h2 x y)))

   (defthm hh3
     (implies (and (not (c1 x y))
                   (not (c2 x y))
                   (c3 x y))
              (h3 x y)))

   (defthm hh0
     (implies (and (not (c1 x y))
                   (not (c2 x y))
                   (not (c3 x y)))
              (h0 x y)))

   (defthm gc1
     (implies (gamma-f x y)
              (gamma-c1 x y)))

   (defthm gc2
     (implies (and (gamma-f x y)
                   (not (c1 x y)))
              (gamma-c2 x y)))

   (defthm gc3
     (implies (and (gamma-f x y)
                   (not (c1 x y))
                   (not (c2 x y)))
              (gamma-c3 x y)))

   (defthm gf1
     (implies (and (gamma-f x y)
                   (c1 x y))
              (gamma-f1 x y)))

   (defthm gf2
     (implies (and (gamma-f x y)
                   (not (c1 x y))
                   (c2 x y))
              (gamma-f2 x y)))

   (defthm gf3
     (implies (and (gamma-f x y)
                   (not (c1 x y))
                   (not (c2 x y))
                   (c3 x y))
              (gamma-f3 x y)))

   (defthm gf0
     (implies (and (gamma-f x y)
                   (not (c1 x y))
                   (not (c2 x y))
                   (not (c3 x y)))
              (gamma-f0 x y)))) ; end of ENCAPSULATE

 (casesplit f
            ((c1 x y) (c2 x y) (c3 x y))
            (f-f1 f-f2 f-f3 f-f0))

 (assert! (function-namep 'f{1} (w state)))

 (assert! (theorem-namep 'f-~>-f{1} (w state))))
