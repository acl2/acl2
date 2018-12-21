;; ===================================================================
;; 
;; Copyright (C) 2018, David Greve
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms of
;; the 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.
;; 
;; ===================================================================
(in-package "ACL2")

;; ===================================================================
;; This book was inspired by the following comment in linear-a.lisp
;; from the ACL2 source code:
;; ===================================================================

; Note that in Multiplication by Positive Preserves Inequality we require the
; positive to be rational.  Multiplication by a "positive" complex rational
; does not preserve the inequality.  For example, the following evaluates
; to nil:
; (let ((c #c(1 -10))
;       (x #c(1 1))
;       (y #c(2 -2)))
;  (implies (and ; (rationalp c)          ; omit the rationalp hyp
;                  (< 0 c))
;           (iff (< x y)                  ; t
;                (< (* c x) (* c y)))))   ; nil

; Thus, the coefficients in our polys must be rational.

;; ===================================================================
;; And if we trace the linear functions in ACL2 we see that terms of
;; the form (* #c(a b) x) are treated as atomic terms .. the complex 
;; number is *not* treated as a coefficient.
;;
;; Note, however, that
;;
;; (* #(c a b) x) 
;;
;; is the same as
;;
;; (+ (* a x) (* b #(c 0 1) x))
;;
;; In other words, we can always decompose complex constants into
;; real and imaginary components (each with rational coefficients)
;; and perform linear reasoning on the fragments.
;;
;; Of course, complex numbers are sufficiently uncommon in ACL2 that
;; it is not worth the additional complexity and effort to extend the
;; linear procedure to do this natively.
;;
;; So that is what this library is for.  It introduces the function
;; (imaginary) as a stand-in for the complex number #c(0 1) and then
;; reduces complex coefficients into their rational and imaginary
;; components.
;;
;; ===================================================================


(encapsulate
    ()

  (local (include-book "workshops/2006/cowles-gamboa-euclid/Euclid/ed5aa" :dir :system))

  ;; These facts were hard to find in the books ..

  (defthm realpart-*
    (equal (realpart (* x y))
           (- (* (realpart x)
                 (realpart y))
              (* (imagpart x)
                 (imagpart y)))))
  
  (defthm imagpart-*
    (equal (imagpart (* x y))
           (+ (* (realpart x)
                 (imagpart y))
              (* (imagpart x)
                 (realpart y)))))

  )

(local
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm imagpart-complex-force
     (implies
      (case-split
       (and
        (rationalp x)
        (rationalp y)))
      (equal (imagpart (complex x y))
             y))))

  (local
   (defthm realpart-complex-force
     (implies
      (case-split
       (and
        (rationalp x)
        (rationalp y)))
      (equal (realpart (complex x y))
             x))))

  (defthm equal-complex-to-equal-parts
    (iff (equal (complex real imag) z)
         (and (acl2-numberp z)
              (equal (rfix real) (realpart z))
              (equal (rfix imag) (imagpart z)))))

  (defthmd equal-complex-to-equal-parts-z
    (implies
     (complex-rationalp c)
     (iff (equal c z)
          (and (acl2-numberp z)
               (equal (realpart c) (realpart z))
               (equal (imagpart c) (imagpart z)))))
    :hints (("Goal" :use (:instance equal-complex-to-equal-parts
                                    (real (realpart c))
                                    (imag (imagpart c))))))
    
  ))

(defun imaginary ()
  (complex 0 1))

(in-theory (disable (:type-prescription imaginary)))

(defthm imaginary-type
  (acl2-numberp (imaginary))
  :rule-classes (:type-prescription))

(defthm realpart-imaginary
  (equal (realpart (imaginary))
         0))

(defthm imagpart-imaginary
  (equal (imagpart (imaginary))
         1))

(defthm imaginary-product-2
  (equal (* (imaginary) (imaginary))
         -1))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm imaginary-product-3
    (equal (* (imaginary) (* (imaginary) x))
           (* -1 x)))
  
  )

(encapsulate
    ()
  
  (local
   (encapsulate
       ()
     
     (local (include-book "arithmetic-5/top" :dir :system))
     
     (defthmd open-mod-4
       (implies
        (and 
         (syntaxp (symbolp x))
         (natp x))
        (equal (mod x 4)
               (if (<= 4 x)
                   (mod (- x 4) 4)
                 x))))
     
     (defthm move-constants
       (implies
        (syntaxp (and (not (quotep x)) (quotep y)))
        (equal (* x (* y z))
               (* y (* x z)))))
     
     ))
  
  (local
   (encapsulate
       ()

     (defun mod4 (n)
       (let ((n (nfix n)))
         (cond
          ((equal n 0) 0)
          ((equal n 1) 1)
          ((equal n 2) 2)
          ((equal n 3) 3)
          (t (mod4 (- n 4))))))
     
     (defthm equal-mod4-mod4
       (implies
        (natp x)
        (equal (mod x 4)
               (mod4 x)))
       :hints (("Goal" :induct (mod4 x)
                :in-theory (e/d (open-mod-4) (mod)))))
     
     (defthm alt-expt-definition
       (implies
        (and
         (syntaxp (symbolp n))
         (natp n))
        (equal (expt x n)
               (let ((x (fix x)))
                 (cond
                  ((equal n 0) 1)
                  ((equal n 1) x)
                  ((equal n 2) (* x x))
                  ((equal n 3) (* x x x))
                  (t (* x x x x (expt x (- n 4))))))))
       :rule-classes (:definition)
       :hints (("Goal" :do-not-induct t
                :expand ((expt x 3) (expt x 2) (expt x 1)))
               (and stable-under-simplificationp
                    `(:expand (expt x n)))
               (and stable-under-simplificationp
                    `(:expand (expt x (+ -1 n))))
               (and stable-under-simplificationp
                    `(:expand (expt x (+ -2 n))))
               ))
     
     (defthm collect-constants
       (implies
        (syntaxp (and (quotep x) (quotep y)))
        (equal (* x (* y z))
               (* (* x y) z))))
     
     ))
  
  (defthm expt-imaginary
    (implies
     (natp n)
     (equal (expt (imaginary) n)
            (let ((n (mod n 4)))
              (cond
               ((equal n 0) 1)
               ((equal n 1) (imaginary))
               ((equal n 2) -1)
               (t (- (imaginary)))))))
    :hints (("Goal" :induct (mod4 n)
             :in-theory (disable mod expt (imaginary) imaginary))
            (and stable-under-simplificationp
                 '(:expand (
                            (:free (x) (expt x 0))
                            (:free (x) (expt x 1))
                            (:free (x) (expt x 2))
                            (:free (x) (expt x 3))
                            )))))
  )

(encapsulate
    ()
  
  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm complex-to-imaginary
    (equal (complex real imag)
           (+ (rfix real) (* (rfix imag) (imaginary)))))
  
  (defthm reduce-complex-coefficient
    (implies
     (and
      (syntaxp (quotep c))
      (complex-rationalp c))
     (equal (* c x)
            (+ (* (realpart c) x) (* (imagpart c) (imaginary) x))))
    :hints (("Goal" :in-theory (enable equal-complex-to-equal-parts-z))))

  )

(in-theory (disable imaginary (imaginary)))

(local
 ;; Note: this theorem was not provable (by linear) prior to loading this book
 (defthm complex-poly-test
   (implies
    (and
     (acl2-numberp x)
     (acl2-numberp y)
     (< 0 (+ (* #C( 1  2) x) (* #C(4  3) y)))
     (< 0 (+ (* #C(-1 -2) x) (* #C(0 -3) y)))
     (< 0 (+ (- y) -2))
     )
    nil)
   :rule-classes nil)
 )

