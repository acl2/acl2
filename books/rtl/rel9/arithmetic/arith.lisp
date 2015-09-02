; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

;This book contains basic arith stuff which i'm pretty sure won't hurt anything.

(local (include-book "arith2"))

;This is a meta rule to cancel identical terms from both sides of an equality of sums.
(include-book "../../../meta/meta-plus-equal")

;This is a meta rule to cancel identical terms from both sides of a < of sums.
(include-book "../../../meta/meta-plus-lessp")

;This is a meta rule to cancel identical terms from both sides of an equality of products (I think).
(include-book "../../../meta/meta-times-equal")

;Note!  There is not meta-times-lessp, which would be really nice to have.  I now have a bind-free rule to do that...

(defthm collect-constants-in-equal-of-sums
  (implies (and (syntaxp (and (quotep c1) (quotep c2)))
                (case-split (acl2-numberp c1))
                )
           (and (equal (equal (+ c2 x) c1)
                       (equal (fix x) (- c1 c2)))
                (equal (equal c1 (+ c2 x))
                       (equal (fix x) (- c1 c2))))))

(defthm collect-constants-in-equal-of-sums-2
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (and (equal (equal (+ c2 x) (+ c1 y))
                       (equal (fix x) (+ (- c1 c2) y))))))

(defthm collect-constants-in-<-of-sums
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (and (equal (< (+ c2 x) c1)
                       (< x (- c1 c2)))
                (equal (< c1 (+ c2 x))
                       (< (- c1 c2) x)))))

(defthm collect-constants-in-<-of-sums-2
  (implies (syntaxp (and (quotep c1) (quotep c2)))
           (equal (< (+ c2 x) (+ c1 y))
                  (< x (+ (- c1 c2) y)))))

;I put this in because it seems to help rewrite stupid hyps quickly.
(defthm dumb
  (equal (< x x)
         nil))
