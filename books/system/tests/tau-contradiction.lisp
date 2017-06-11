; Copyright (C) 2017, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file, contributed by Matt Kaufmann and J Moore, is based on an example
; sent by Grant Passmore.

(in-package "ACL2")

; Grant's example:

(defun f (x) (> x 0))
(defun g (x) (< x 0))
(defun h (x) (and (f x) (g x)))

(assert-event
 (equal (getpropc 'h 'pos-implicants nil (w state))
        *contradictory-tau*))

; This is proved using only tau:
(defthm h-implies-consp
  (implies (h x) (consp x))
  :hints (("Goal" :in-theory '((:e tau-system)))))

(assert-event
 (equal (getpropc 'h 'pos-implicants nil (w state))
        *contradictory-tau*))
