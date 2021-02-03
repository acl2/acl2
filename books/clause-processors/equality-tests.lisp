; Equality Substitution Clause Processor
; Copyright (C) 2007-2010 Kookamara LLC

; See equality.lisp (which was the original source of the test below).

(in-package "ACL2")

(include-book "equality")

; Matt K. mod: Avoid ACL2(p) error from p-thm (clause-processor returns more
; than two values).
(set-waterfall-parallelism nil)

; Here is an application contributed by Erik Reeber (which we make local so
; that it's not exported).

(local
 (progn

   (encapsulate
    (((f *) => *)
     ((g *) => *)
     ((p * *) => *))
    (local (defun f (x) x))
    (local (defun g (x) x))
    (local (defun p (x y) (declare (ignore x y)) t))
    (defthm p-axiom (p (g x) (g y))))

   (local (include-book "std/testing/must-fail" :dir :system))

   (must-fail ; illustrates why we need a hint
    (defthm p-thm-fail
      (implies (and (equal (f x) (g x))
                    (equal (f y) (g y)))
               (p (f x) (f y)))))

   (defthm p-thm
     (implies (and (equal (f x) (g x))
                   (equal (f y) (g y)))
              (p (f x) (f y)))
     :hints (("Goal"
              :clause-processor
              (:function
               equality-substitute-clause
               :hint
; The following is an alist with entries (old . new), where new is to be
; substituted for old.
               '(((f x) . (g x))
                 ((f y) . (g y)))))))
   ))
