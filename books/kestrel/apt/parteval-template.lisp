; APT Partial Evaluation Transformation -- Template
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Formalization in ACL2 of the template functions, theorems, and proofs
; in the design notes, for the non-recursive case, for n = m = 1.

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
  :hints (("Goal" :in-theory nil :use (f f1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Formalization in ACL2 of the template functions, theorems, and proofs
; in the design notes, for the recursive case, for n = m = 1,
; using 'g' instead of 'f'.
; We use a constrained function for the unspecified body of f,
; so the recursive case is not too different from the non-recursive one above.

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
  :hints (("Goal" :in-theory nil :use g1)))
