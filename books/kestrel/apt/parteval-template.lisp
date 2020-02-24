; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Formalization in ACL2 of the template functions, theorems, and proofs
; in the design notes, for the non-recursive case, for n = m = 1.

(must-succeed*

 (defstub e-guard (* *) => *) ; \gamma_e in the design notes

 (encapsulate
   (((e * *) => * :formals (x y) :guard (e-guard x y)))
   (local (defun e (x y) (cons x y))))

 (encapsulate
   (((f-guard-guard * *) => *)) ; \gamma_{\gamma_f} in the design notes
   (local (defun f-guard-guard (x y) (cons x y)))
   (defthm f-guard-guard-always-holds (f-guard-guard x y)))

 (encapsulate
   (((f-guard * *) => * ; \gamma_f in the design notes
     :formals (x y) :guard (f-guard-guard x y)))
   (local (defun f-guard (x y) (e-guard x y)))
   (defthm f-guard-verified (implies (f-guard x y) (e-guard x y))))

 (defun f (x y)
   (declare (xargs :guard (f-guard x y)
                   :guard-hints (("Goal"
                                  :in-theory nil
                                  :use (f-guard-guard-always-holds
                                        f-guard-verified)))))
   (e x y))

 (defstub y~ () => *)

 (defun f1 (x)
   (declare
    (xargs :guard (f-guard x (y~))
           :guard-hints (("Goal"
                          :in-theory nil
                          :use (:instance (:guard-theorem f) (y (y~)))))))
   (e x (y~)))

 (defthm f-f1 ; ff' in the design notes
   (implies (equal y (y~))
            (equal (f x y)
                   (f1 x)))
   :hints (("Goal" :in-theory '(f f1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Formalization in ACL2 of the template functions, theorems, and proofs
; in the design notes, for the recursive case, default treatment, for n = m = 1,
; using 'g' instead of 'f'.
; We use a constrained function for the unspecified body of f,
; so the recursive case is not too different from the non-recursive one above.

(must-succeed*

 (defstub g-body-guard (* *) => *) ; guard of the body

 (encapsulate
   (((g-body * *) => * ; uninterpreted body
     :formals (x y) :guard (g-body-guard x y)))
   (local (defun g-body (x y) (cons x y))))

 (encapsulate
   (((g-guard-guard * *) => *)) ; \gamma_{\gamma_f} in the design notes
   (local (defun g-guard-guard (x y) (cons x y)))
   (defthm g-guard-guard-always-holds (g-guard-guard x y)))

 (encapsulate
   (((g-guard * *) => * ; \gamma_f in the design notes
     :formals (x y) :guard (g-guard-guard x y)))
   (local (defun g-guard (x y) (g-body-guard x y)))
   (defthm g-guard-verified (implies (g-guard x y) (g-body-guard x y))))

 (defun g (x y) ; f in the design notes
   (declare (xargs :guard (g-guard x y)
                   :guard-hints (("Goal"
                                  :in-theory nil
                                  :use (g-guard-guard-always-holds
                                        g-guard-verified)))))
   (g-body x y))

 (defstub y~ () => *)

 (defun g1 (x) ; f' in the design notes
   (declare
    (xargs :guard (g-guard x (y~))
           :guard-hints (("Goal"
                          :in-theory nil
                          :use (:instance (:guard-theorem g) (y (y~)))))))
   (g x (y~)))

 (defthm g-g1 ; ff' in the design notes
   (implies (equal y (y~))
            (equal (g x y)
                   (g1 x)))
   :hints (("Goal" :in-theory '(g1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Formalization in ACL2 of the template functions, theorems, and proofs
; in the design notes, for the recursive case with unchanging static arguments,
; for n = m = 1.

(must-succeed*

 ;; constituents of f, without guards:

 (encapsulate

   (((a * *) => *)
    ((b * *) => *)
    ((c * * *) => *)
    ((d * *) => *)
    ((mu *) => *))

   (local (defun a (x y) (declare (ignore y)) (zp x)))
   (local (defun b (x y) (declare (ignore x y)) nil))
   (local (defun c (x y z) (declare (ignore x y z)) nil))
   (local (defun d (x y) (declare (ignore y)) (1- x)))
   (local (defun mu (x) (acl2-count x)))

   (defthm tau
     (and (o-p (mu x))
          (implies (not (a x y))
                   (o< (mu (d x y))
                       (mu x))))
     :rule-classes nil)) ; end of ENCAPSULATE

 ;; definition of f, without guards:

 (defund f (x y)
   (declare (xargs :measure (mu x)
                   :hints (("Goal" :in-theory nil :use tau))))
   (if (a x y)
       (b x y)
     (c x y (f (d x y) y))))

 ;; constant value for the static parameter:

 (defstub y~ () => *)

 ;; definition of f' without guards, with termination proof:

 (defund fprime (x)
   (declare (xargs :measure (mu x)
                   :hints (("Goal"
                            :in-theory nil
                            :use (:instance (:termination-theorem f)
                                  (y (y~)))))))
   (if (a x (y~))
       (b x (y~))
     (c x (y~) (fprime (d x (y~))))))

 ;; correctness of f':

 (defthmd f-fprime
   (implies (equal y (y~))
            (equal (f x y)
                   (fprime x)))
   :hints (("Goal" :in-theory '(fprime f) :induct (fprime x))))

 ;; guarded constituents of f, constrained equal to the unguarded ones,
 ;; and constrained so that (the guarded version of) f is guard-verified:

 (encapsulate

   (((ag * *) => * :formals (x y) :guard (gamma-a x y))
    ((bg * *) => * :formals (x y) :guard (gamma-b x y))
    ((cg * * *) => * :formals (x y z) :guard (gamma-c x y z))
    ((dg * *) => * :formals (x y) :guard (gamma-d x y))
    ((gamma-a * *) => *)
    ((gamma-b * *) => *)
    ((gamma-c * * *) => *)
    ((gamma-d * *) => *)
    ((gamma-f * *) => *))

   (local (defun ag (x y) (a x y)))
   (local (defun bg (x y) (b x y)))
   (local (defun cg (x y z) (c x y z)))
   (local (defun dg (x y) (d x y)))
   (local (defun gamma-a (x y) (declare (ignore x y)) t))
   (local (defun gamma-b (x y) (declare (ignore x y)) t))
   (local (defun gamma-c (x y z) (declare (ignore x y z)) t))
   (local (defun gamma-d (x y) (declare (ignore x y)) t))
   (local (defun gamma-f (x y) (declare (ignore x y)) t))

   (defthmd ag=a (equal (ag x y) (a x y)))
   (defthmd bg=b (equal (bg x y) (b x y)))
   (defthmd cg=c (equal (cg x y z) (c x y z)))
   (defthmd dg=d (equal (dg x y) (d x y)))

   (defthm a-guard-sat
     (implies (gamma-f x y)
              (gamma-a x y))
     :rule-classes nil)

   (defthm b-guard-sat
     (implies (and (gamma-f x y)
                   (a x y))
              (gamma-b x y))
     :rule-classes nil)

   (defthm c-guard-sat
     (implies (and (gamma-f x y)
                   (not (a x y)))
              (gamma-c x y (f (d x y) y)))
     :rule-classes nil)

   (defthm d-guard-sat
     (implies (and (gamma-f x y)
                   (not (a x y)))
              (gamma-d x y))
     :rule-classes nil)

   (defthm f-guard-rec-sat
     (implies (and (gamma-f x y)
                   (not (a x y)))
              (gamma-f (d x y) y)))) ; end of ENCAPSULATE

 ;; guarded version of f, proved to be equal to f:

 (defund fg (x y)
   (declare (xargs :guard (gamma-f x y)
                   :verify-guards nil ; done below
                   :measure (mu x)
                   :hints (("Goal" :in-theory '(ag=a dg=d) :use tau))))
   (if (ag x y)
       (bg x y)
     (cg x y (fg (dg x y) y))))

 (defthmd fg=f
   (equal (fg x y)
          (f x y))
   :hints (("Goal" :in-theory '(f fg ag=a bg=b cg=c dg=d) :induct (fg x y))))

 ;; the guard-related constraints ensure that
 ;; (the guarded version of) f is guard-verified:

 (verify-guards fg
   :hints (("Goal"
            :in-theory '(ag=a dg=d fg=f)
            :use (a-guard-sat
                  b-guard-sat
                  c-guard-sat
                  d-guard-sat
                  f-guard-rec-sat))))

 ;; guarded version of f', proved to be equal to f':

 (defund fprimeg (x)
   (declare (xargs :guard (gamma-f x (y~))
                   :verify-guards nil ; done below
                   :measure (mu x)
                   :hints (("Goal"
                            :in-theory '(ag=a dg=d)
                            :use (:termination-theorem fprime)))))
   (if (ag x (y~))
       (bg x (y~))
     (cg x (y~) (fprimeg (dg x (y~))))))

 (defthmd fprimeg=fprime
   (equal (fprimeg x)
          (fprime x))
   :hints (("Goal"
            :in-theory '(fprime fprimeg ag=a bg=b cg=c dg=d fg=f)
            :induct (fprimeg x))))

 ;; rephrasing of the ff' theorem for the guarded versions of f and f':

 (defthmd fg-fprimeg
   (implies (equal y (y~))
            (equal (fg x (y~))
                   (fprimeg x)))
   :hints (("Goal" :in-theory '(fg=f fprimeg=fprime f-fprime))))

 ;; guard verification proof of (the guarded version of) f':

 (verify-guards fprimeg
   :hints (("Goal"
            :in-theory nil
            :use ((:instance (:guard-theorem fg) (y (y~)))
                  (:instance fg-fprimeg (x (dg x (y~))) (y (y~))))))))
