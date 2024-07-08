;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "util")

;; This is bound on the maximum delay caused by the following scenario:

;;       A           B           C
;; |           |           |           |
;; +-----------+-----------+-----------+
;;    |     B'    |     C'    |
;;
;;  A                    B  CD
;; |>          |          <|><        ;; UAV's x+1 and x+2 meet just after x and x+1 split
;; |>          |          <|<<        
;; |    >      |      < <  |       
;; |    A      |      B C  |
;; |          >|< <<       |
;; |          <|><|>       |
;; |          <|<<|>       |
;;            A BC D

;;
;; e = (n+1)*ss' - n*ss
;;
;; delay = n*ss' - (n-1)*ss - e
;;
;; (n+1)*ss' - n*ss = 0
;;
;; ss' = n*ss/(n+1)
;;
;; delay = n*n*ss/(n+1) - (n-1)*ss
;;       = ss*((n*n) - (n-1)*(n+1))/(n+1)
;;
;; n*n - (n*n - 1)
;;
;; delay = ss/(n+1)
;;

(def::un err (n ss ssp)
  (declare (xargs :fty ((pos prat prat) rational)))
  (- (* (+ n 1) ssp) (* n ss)))

(local (in-theory (enable prat-p)))

(def::un ssp (n ss)
  (declare (xargs :fty ((pos prat) prat)))
  (/ (* n ss) (+ n 1)))

(with-arithmetic
 (defthm err-of-ssp
   (equal (err n ss (ssp n ss)) 0)))

(in-theory (disable err ssp))

(def::un delay (n ss ssp e)
  (declare (xargs :fty ((pos prat prat nnrat) rational)))
  (- (* n ssp) (+ (* (1- n) ss) e)))

(include-book "math")

(with-arithmetic
 (defthm delay-is-differnce-in-seg-size
   (implies
    (<= 0 (err n ss ssp))
    (equal (delay n ss ssp (err n ss ssp))
           (- (prat-fix ss) (prat-fix ssp))))
   :hints (("Goal" :in-theory (enable err)))))

(with-arithmetic
 (defthm delay-is-reduced-by-initial-error
   (implies
    (<= 0 (err n ss ssp))
    (equal (delay n ss ssp (+ (prat-fix e) (err n ss ssp)))
           (- (prat-fix ss) (+ (prat-fix e) (prat-fix ssp)))))
   :hints (("Goal" :in-theory (enable err)))))

(with-arithmetic
 (defthm maximum-initial-delay
   (equal (delay n ss (ssp n ss) (err n ss (ssp n ss)))
          (/ (prat-fix ss) (+ (pos-fix n) 1)))
   :hints ((stable-p :in-theory (enable ssp remove-reciporicals-=)))))
