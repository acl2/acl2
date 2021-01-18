; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Nathan Guermond (guermond@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "twisted-edwards-closure-core")

(include-book "kestrel/crypto/ecurve/points" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Closure Proof of Simplified Twisted Edwards Addition
; ----------------------------------------------------

; In this book we prove the closure of
; a simplified group addition on twisted Edwards curves.
; We use the core proof in twisted-edwards-closure-core.lisp.
; The adjective 'simplified' above refers to the fact that
; the addition operation is a somewhat simplified one,
; compared to the twisted-edwards-add operation:
; the simplified one is based on the constrained (prime)
; from the odd prime fields library,
; and takes the a, c, and d coefficients as parameters
; instead of a curve (of the twisted-edwards-curve fixtype) as parameter;
; however, the simplified operation works on points,
; not just coordinates like the core proof.
; Note that the c parameter is present because the core proof is based on that;
; a twisted Edwards curve has no c coefficient.

; Besides a simplified addition operation,
; here we also define a simplified predicate to check
; whether a point is on the curve (compared to point-on-twisted-edwards-p).
; This has the same kind of simplifications as the addition operation.

; This file is meant to be included only locally in larger developments
; (or non-locally in a file that is included locally);
; the names of the functions and theorems are too generic.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Simplified predicate to check if a point is on a curve.

(defund simp-point-on-curve-p (point a c d)
  (and (not (eq point :infinity))
       (let ((x (car point))
             (y (cdr point)))
         (ECp x y a c d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Simplified addition operation.

(defund simp-curve-add (pt1 pt2 a c d)
  (let ((y1 (cdr pt1))
        (y2 (cdr pt2))
        (x1 (car pt1))
        (x2 (car pt2)))
    (cons (modp (x3$)) (modp (y3$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof that the result of addition is a point.

(defthmd pointp-of-simp-curve-add
  (pointp (simp-curve-add pt1 pt2 a c d))
  :hints (("Goal" :in-theory (enable simp-curve-add pointp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Proof that the result of addition is in the field cartesian product.

(defthmd simp-point-in-pxp-p-of-simp-curve-add
  (implies (and (point-in-pxp-p pt1 (prime))
                (point-in-pxp-p pt2 (prime)))
           (point-in-pxp-p (simp-curve-add pt1 pt2 a c d) (prime)))
  :hints (("Goal" :in-theory (enable point-in-pxp-p
                                     simp-curve-add))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Closure proof of simplified addition, expressed via the simplified predicate.

(defthmd closure-of-simp-curve-add
  (implies (and (domain)
                (not (=p a 0))
                (non-square d)
                (=p (sq sqrt{a}) a)
                (integerp sqrt{a})
                (not (=p c 0))
                (pointp pt1)
                (pointp pt2)
                (point-in-pxp-p pt1 (prime))
                (point-in-pxp-p pt2 (prime))
                (simp-point-on-curve-p pt1 a c d)
                (simp-point-on-curve-p pt2 a c d))
           (and (pointp (simp-curve-add pt1 pt2 a c d))
                (point-in-pxp-p (simp-curve-add pt1 pt2 a c d) (prime))
                (simp-point-on-curve-p (simp-curve-add pt1 pt2 a c d) a c d)))
  :hints (("Goal" :in-theory (enable pointp
                                     simp-point-on-curve-p
                                     point-in-pxp-p
                                     simp-curve-add)
           :use (:instance main-theorem
                           (x1 (car pt1))
                           (x2 (car pt2))
                           (y1 (cdr pt1))
                           (y2 (cdr pt2))))))
