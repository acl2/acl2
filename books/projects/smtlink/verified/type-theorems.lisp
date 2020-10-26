;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 16th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")

(defthm equal-theorem
  (implies t
           (booleanp (equal x y))))

(defthm <-theorem
  (implies t
           (booleanp (< x y))))

(defthm binary-+-of-integerp
  (implies (and (integerp x) (integerp y))
           (integerp (binary-+ x y))))

(defthm binary-+-of-rational-integerp
  (implies (and (rationalp x) (integerp y))
           (rationalp (binary-+ x y))))

(defthm binary-+-of-integer-rationalp
  (implies (and (rationalp x) (integerp y))
           (rationalp (binary-+ x y))))

(defthm binary-+-of-rationalp
  (implies (and (rationalp x) (rationalp y))
           (rationalp (binary-+ x y))))

(defthm unary---of-integerp
  (implies (integerp x)
           (integerp (unary-- x))))

(defthm unary---of-rationalp
  (implies (rationalp x)
           (rationalp (unary-- x))))

(defthm binary-*-of-integerp
  (implies (and (integerp x) (integerp y))
           (integerp (binary-* x y))))

(defthm binary-*-of-rational-integerp
  (implies (and (rationalp x) (integerp y))
           (rationalp (binary-* x y))))

(defthm binary-*-of-integer-rationalp
  (implies (and (rationalp x) (integerp y))
           (rationalp (binary-* x y))))

(defthm binary-*-of-rationalp
  (implies (and (rationalp x) (rationalp y))
           (rationalp (binary-* x y))))

(defthm unary-/-of-integerp
  (implies (integerp x)
           (rationalp (unary-/ x))))

(defthm unary-/-of-rationalp
  (implies (rationalp x)
           (rationalp (unary-/ x))))

(defthm not-theorem
  (implies (booleanp x)
           (booleanp (not x))))

(encapsulate (((type-p *) => *))
  (local (defun type-p (x)
           (integerp x)))

  (defthm if-theorem
    (implies (and (booleanp cond)
                  (type-p then)
                  (type-p else))
             (type-p (if cond then else ))))
  )

(defthm implies-theorem
  (implies (and (booleanp antecedent)
                (booleanp consequence))
           (booleanp (implies antecedent consequence))))
