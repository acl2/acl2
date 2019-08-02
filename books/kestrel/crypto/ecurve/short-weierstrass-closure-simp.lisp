; Elliptic Curve Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Nathan Guermond (guermond@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "points")
(include-book "short-weierstrass-closure-lemma")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Simplified Elliptic Curve Addition Closure
; ------------------------------------------

; In this book we define "simplified" versions of the functions
; point-on-elliptic-curve-p and curve-group-+ from short-weierstrass.lisp by
; encapsulating some of the arithmetic using our previously defined polynomials
; in short-weierstrass-lemma.lisp. We then prove the closure property for these
; simplified definitions, which short-weierstrass.lisp then uses to prove the
; closure property on the original definitions of the two aforementioned
; functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We first prove the following simplification theorem:
;;   y1 p/= - y2, P[x1,y1] =p 0, P[x2,y2] =p 0 --> y1 =p y2.

;; If two points have the same x coordinate, and the y coordinates are not
;; inverses, then the y coordinate are the same (because the y coordinate is
;; squared in the curve equation).  This is used below in
;; simp-closure-of-curve-group-+.

(defthmd x1=x2-implies-y1=y2-when-y1+y2=/=0
  (implies (and (integerp A)
                (integerp B)
                (integerp x1)
                (integerp x2)
                (integerp y1)
                (integerp y2)
                (=p x1 x2)
                (not (=p (i+ y1 y2) 0))
                (=p (P[X.Y] x1 y1 A B) 0)
                (=p (P[X.Y] x2 y2 A B) 0))
           (=p y1 y2))
  :hints (("Goal"
           :in-theory (e/d (P[X.Y]) (=p-implies-=p-i+-1
                                     =p-implies-=p-i+-2
                                     =p-of-i+-and-i+-cancel))
           :use ((:instance =p-implies-=p-i+-2
                  (x (i- (i+ B (i* A x1) (icube x1))))
                  (y (i+ B (i* A x1) (i- (isqr y1)) (icube x1)))
                  (y-equiv (i+ B (i* A x1) (i- (isqr y2)) (icube x1))))
                 (:instance |x^2 =p y^2 --> x =p y or x =p -y|
                  (x y1)
                  (y y2))
                 (:instance =p-implies-=p-i+-1
                  (y y2)
                  (x y1)
                  (x-equiv (i- y2)))
                 (:instance |-x =p -y --> x =p y|
                  (x (isqr y1))
                  (y (isqr y2)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Simplified definitions of point-on-elliptic-curve-p and curve-group-+.

;; The following definitions are based on P[X.Y], alpha{x1=x2}, alpha{x1=/=x2},
;; which are disabled, thus greatly simplifying proofs.

(defund simp-point-on-elliptic-curve-p (point a b)
  (let ((x (car point)) (y (cdr point)))
    (or (equal point '(0 . 0))
        (=p (P[X.Y] x y a b) 0))))

(defund simp-curve-group-+ (point1 point2 a b)
  (declare (ignorable a b))
  (if (equal point1 '(0 . 0))
      point2
    (if (equal point2 '(0 . 0))
        point1
      (let ((x1 (car point1)) (x2 (car point2))
            (y1 (cdr point1)) (y2 (cdr point2)))
        (if (and (=p x1 x2)
                 (=p (i+ y1 y2) 0))
            '(0 . 0)
          (if (=p x1 x2)
              (let* ((slope (alpha{x1=x2} x1 y1 a))
                     (x3 (x3 slope x1 x2))
                     (y3 (y3 slope x1 y1 x2)))
                (cons (modp x3) (modp y3)))
            (let* ((slope (alpha{x1=/=x2} x1 y1 x2 y2))
                   (x3 (x3 slope x1 x2))
                   (y3 (y3 slope x1 y1 x2)))
              (cons (modp x3) (modp y3)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Closure proof for the "simplified" (in the aforementioned sense) functions.

(local
 (defthmd lemma
   (implies (and (=p y1 0)
                 (=p y1 y2))
            (=p (i+ y1 y2) 0))))

(defthmd simp-closure-of-curve-group-+
  (implies (and (integerp a)
                (integerp b)
                (pointp point1)
                (pointp point2)
                (simp-point-on-elliptic-curve-p point1 a b)
                (simp-point-on-elliptic-curve-p point2 a b))
           (simp-point-on-elliptic-curve-p
            (simp-curve-group-+ point1 point2 a b) a b))
  :hints (("Goal"
           :in-theory (enable simp-curve-group-+
                              simp-point-on-elliptic-curve-p
                              pointp)
           :use ((:instance P[X1.Y1]=0-and-P[X2.Y2]=0-implies-P[X3.Y3]=0
                  (x1 (car point1))
                  (y1 (cdr point1))
                  (x2 (car point2))
                  (y2 (cdr point2))
                  (alpha (alpha{x1=/=x2} (car point1)
                                         (cdr point1)
                                         (car point2)
                                         (cdr point2))))
                 (:instance x1=x2-implies-y1=y2-when-y1+y2=/=0
                  (x1 (car point1))
                  (x2 (car point2))
                  (y1 (cdr point1))
                  (y2 (cdr point2)))
                 (:instance P[X1.Y1]=0-and-P[X2.Y2]=0-implies-P[X3.Y3]=0
                  (x1 (car point1))
                  (y1 (cdr point1))
                  (x2 (car point2))
                  (y2 (cdr point2))
                  (alpha (alpha{x1=x2} (car point1) (cdr point1) a)))
                 (:instance lemma (y1 (cdr point1)) (y2 (cdr point2)))))))

(defthmd pointp-and-point-in-pxp-p-of-simp-curve-group-+
  (implies (and (pointp point1)
                (pointp point2)
                (point-in-pxp-p point1 (prime))
                (point-in-pxp-p point2 (prime)))
           (and (pointp (simp-curve-group-+ point1 point2 a b))
                (point-in-pxp-p (simp-curve-group-+ point1 point2 a b) (prime))))
  :hints (("Goal" :in-theory (e/d (simp-curve-group-+ pointp point-in-pxp-p)))))
