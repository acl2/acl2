; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann in consultation with Cuong Chau, April, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; cert_param: (uses-acl2r)

(in-package "ACL2")

; Formalization of the overspill property in ACL2(r)

; In order to apply overspill-p-overspill (at the end, below) to one's own
; predicate, (p0 i x), I expect the following approach to suffice.  First,
; define p0* and p0-witness in analogy to overspill-p* and overspill-p-witness
; below, respectively.  Second, functionally instantiate overspill-p-overspill.
; Now, suppose that you prove a theorem of the form:

;   (implies (and (hyps x) (natp i) (standardp i))
;            (p0 i x))

; Then you can easily conclude the following from your functional instance of
; overspill-p-overspill, saying that p0 "overspills" to some nonstandard n:

;   (implies (hyps x)
;            (let ((n (overspill-p-witness x)))
;              (and (natp n)
;                   (overspill-p n x)
;                   (i-large n)))

(local (include-book "overspill-proof"))

(set-enforce-redundancy t)

(defstub overspill-p (n x) t)

(defun overspill-p* (n x)
  (if (zp n)
      (overspill-p 0 x)
    (and (overspill-p n x)
         (overspill-p* (1- n) x))))

(defchoose overspill-p-witness (n) (x)
  (or (and (natp n)
           (standardp n)
           (not (overspill-p n x)))
      (and (natp n)
           (i-large n)
           (overspill-p* n x))))

(defthm overspill-p-overspill
  (let ((n (overspill-p-witness x)))
    (or (and (natp n)
             (standardp n)
             (not (overspill-p n x)))
        (and (natp n)
             (i-large n)
             (implies (and (natp m)
                           (<= m n))
                      (overspill-p m x)))))
  :rule-classes nil)
