; Elliptic Curve Library: Validation of curve-group-+
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; This book shows that the function for point addition, curve-group-+, defined
;; in short-weierstrass.lisp, satisfies Rules 1-5 in Section 2.2.1 of
;; http://www.secg.org/sec1-v2.pdf.

(include-book "short-weierstrass")
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "kestrel/crypto/ecurve/prime-field-intro" :dir :system))

(defthm rule1
  (equal (curve-group-+ '(0 . 0) '(0 . 0) p a b)
         '(0 . 0)))

(defthm rule2a
  (implies (and (natp x)
                (< x p)
                (natp y)
                (< y p))
           (equal (curve-group-+ (cons x y) '(0 . 0) p a b)
                  (cons x y))))

(defthm rule2b
  (implies (and (natp x)
                (< x p)
                (natp y)
                (< y p))
           (equal (curve-group-+ '(0 . 0) (cons x y) p a b)
                  (cons x y))))

(defthm rule3
  (implies (and (natp x)
                (< x p)
                (natp y)
                (< y p)
                (point-in-pxp-p (cons x y) p)
                (posp p))
           (equal (curve-group-+ (cons x y) (cons x (- y)) p a b)
                  '(0 . 0)))
  :hints (("Goal" :in-theory (enable fep curve-group-+))))

(defthm rule4
  (implies (and (natp x1)
                (< x1 p)
                (natp y1)
                (< y1 p)
                (point-in-pxp-p (cons x1 y1) p)
                (natp x2)
                (< x2 p)
                (natp y2)
                (< y2 p)
                (point-in-pxp-p (cons x2 y2) p)
                (not (equal x1 x2))
                (< 2 p)
                (rtl::primep p)
                (integerp a)
                ;; These two assumptions seem justified if the rules are
                ;; interpreted in an ordered way, where the rules about '(0
                ;; . 0) take precedence:
                (not (equal (cons x1 y1) '(0 . 0)))
                (not (equal (cons x2 y2) '(0 . 0))))
           (equal (curve-group-+ (cons x1 y1) (cons x2 y2) p a b)
                  (let ((lamb (div (sub y2 y1 p)
                                   (sub x2 x1 p)
                                   p)))
                    (let ((x3 (sub (sub (mul lamb lamb p) x1 p) x2 p)))
                      (cons x3
                            (sub (mul lamb (sub x1 x3 p) p) y1 p) ;y3
                            )))))
  :hints (("Goal" :in-theory (enable curve-group-+))))

(defthm rule5
  (implies (and (natp x1)
                (< x1 p)
                (natp y1)
                (< y1 p)
                (point-in-pxp-p (cons x1 y1) p)
                (not (equal y1 0))
                (< 2 p)
                (rtl::primep p)
                (integerp a))
           (equal (curve-group-+ (cons x1 y1) (cons x1 y1) p a b)
                  (let ((lamb (div (add (mul 3 (mul x1 x1 p) p) a p)
                                   (mul 2 y1 p)
                                   p)))
                    (let ((x3 (sub (mul lamb lamb p) (mul 2 x1 p) p)))
                      (cons x3
                            (sub (mul lamb (sub x1 x3 p) p) y1 p)   ;y3
                            )))))
  :hints (("Goal" :in-theory (enable pfield::sub-rewrite curve-group-+))))
