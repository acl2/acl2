; Application of the U-substitution rule
;
; Deriving the integral of the function (/ x (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))
;
; Copyright (C) 2022 University of Wyoming
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Main Authors: Jagadish Bapanapally (jagadishb285@gmail.com)
;
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/inequalities" :dir :system))
(include-book "nonstd/nsa/inverse-square" :dir :system)
(include-book "nonstd/nsa/inverse-trig" :dir :system)
(include-book "nonstd/integrals/u-substitution" :dir :system)
(include-book "nonstd/nsa/ln" :dir :system)

(defun int-f-domain() (interval (acl2-sqrt (/ 12 16)) (acl2-sqrt (/ 15 16))))

(defun sub-domain() (interval (/ 1 4) (/ 1 2)))

(defun integral-function (x)
  (if (inside-interval-p x (int-f-domain))
      (/ x (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))
    0))

(defun sub-func (x)
  (if (inside-interval-p x (sub-domain))
      (acl2-sqrt (- 1 (* x x)))
    0))

(defun sub-func-prime (x)
  (if (inside-interval-p x (sub-domain))
      (/ (- x) (acl2-sqrt (- 1 (* x x))))
    0))

(defthm-std int-f-domain-std
  (standardp (int-f-domain)))

(defthm-std sub-domain-std
  (standardp (sub-domain)))

(defthm-std int-func-std
  (implies (standardp x)
           (standardp (integral-function x))))

(defthm-std sub-func-std
  (implies (standardp x)
           (standardp (sub-func x))))

(defthm-std sub-func-prime-std
  (implies (standardp x)
           (standardp (sub-func-prime x))))

(defthmd intervalp-int-f-domain
  (interval-p (int-f-domain)))

(defthmd int-f-domain-real
  (implies (inside-interval-p x (int-f-domain))
	   (realp x)))

(defthmd int-f-domain-non-trivial
  (or (null (interval-left-endpoint (int-f-domain)))
      (null (interval-right-endpoint (int-f-domain)))
      (< (interval-left-endpoint (int-f-domain))
	 (interval-right-endpoint (int-f-domain)))))

(defthmd intervalp-sub-domain
  (interval-p (sub-domain)))

(defthmd sub-domain-real
  (implies (inside-interval-p x (sub-domain))
	   (realp x)))

(defthmd sub-domain-non-trivial
  (or (null (interval-left-endpoint (sub-domain)))
      (null (interval-right-endpoint (sub-domain)))
      (< (interval-left-endpoint (sub-domain))
	 (interval-right-endpoint (sub-domain)))))

(defthmd ineq-lemma1
  (implies (and (realp x1)
                (realp x2)
                (>= x1 0)
                (>= x2 0)
                (> x1 x2))
           (> (* x1 x1) (* x1 x2))))

; matt k. addition to speed up proofs:
(in-theory (disable sqrt-epsilon-delta))

(defthmd ineq-lemma2
  (implies (and (realp x1)
                (realp x2)
                (>= x1 0)
                (>= x2 0)
                (< x2 x1))
           (>= (* x1 x2) (* x2 x2))))

(defthmd ineq-lemma3
  (implies (and (realp a)
                (realp b)
                (realp c)
                (> a b)
                (>= b c))
           (> a c)))

(defthmd ineq-lemma4
  (implies (and (realp x1)
                (realp x2)
                (>= x1 0)
                (>= x2 0)
                (> x1 x2))
           (> (* x1 x1) (* x2 x2)))
  :hints (("goal"
           :use ((:instance ineq-lemma1 (x1 x1) (x2 x2))
                 (:instance ineq-lemma2 (x1 x1) (x2 x2))
                 (:instance ineq-lemma3 (a (* x1 x1)) (b (* x1 x2)) (c (* x2 x2))))
           :in-theory nil
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd sub-func-range-1
    (implies (and (realp x)
                  (realp y)
                  (<= x y)
                  (>= x 0)
                  (>= y 0))
             (<= (* x x) (* y y)))
    :hints (("goal"
             :use ((:instance ineq-lemma4 (x1 y) (x2 x)))
             )))
  )

(defthmd sub-func-range-2
  (implies (and (realp x)
                (<= x (/ 1 2))
                (>= x (/ 1 4)))
           (and (<= (* x x) (/ 1 4))
                (>= (* x x) (/ 1 16))))
  :hints (("goal"
           :use ((:instance sub-func-range-1 (x x) (y (/ 1 2)))
                 (:instance sub-func-range-1 (x (/ 1 4)) (y x)))
           )))

(defthmd sub-func-range-3
  (implies (and (realp x)
                (<= x (/ 1 2))
                (>= x (/ 1 4)))
           (and (<= (- 1 (* x x)) (/ 15 16))
                (>= (- 1 (* x x)) (/ 12 16))))
  :hints (("goal"
           :use ((:instance sub-func-range-2))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd sub-func-range-4
    (implies (realp x)
             (realp (acl2-sqrt x))))

  (defthmd sub-func-range
    (implies (and (realp x)
                  (<= x (/ 1 2))
                  (>= x (/ 1 4)))
             (and (<= (acl2-sqrt (/ 12 16)) (acl2-sqrt (- 1 (* x x))))
                  (<= (acl2-sqrt (- 1 (* x x))) (acl2-sqrt (/ 15 16)))))
    :hints (("goal"
             :use ((:instance sqrt-<-y (x (- 1 (* x x))) (y (acl2-sqrt (/ 15 16))))
                   (:instance y-<-sqrt (x (- 1 (* x x))) (y (acl2-sqrt (/ 12 16))))
                   (:instance y*y=x->y=sqrt-x (x (- 1 (* x x))) (y (acl2-sqrt (/ 15 16))))
                   (:instance y*y=x->y=sqrt-x (x (- 1 (* x x))) (y (acl2-sqrt (/ 12 16))))
                   (:instance sqrt-=-y (x (/ 3 4)) (y (acl2-sqrt (/ 3 4))))
                   (:instance sqrt-=-y (x (/ 15 16)) (y (acl2-sqrt (/ 15 16))))
                   (:instance sub-func-range-3 (x x))
                   (:instance sqrt->-0 (x (/ 15 16)))
                   (:instance sub-func-range-4 (x (/ 15 16)))
                   (:instance sqrt->-0 (x (/ 12 16)))
                   (:instance sub-func-range-4 (x (/ 12 16)))
                   )
             :in-theory nil
             ))))

(defthmd subfunc-range-in-domain-of-int-f
  (implies (inside-interval-p x (sub-domain))
	   (inside-interval-p (sub-func x) (int-f-domain)))
  :hints (("goal"
	   :use ((:instance sub-func-range)
		 (:instance intervalp-int-f-domain)
		 (:instance int-f-domain-real))
	   :in-theory (e/d (interval-definition-theory) (acl2-sqrt))
	   )))

(defthmd int-f-real
  (realp (integral-function x)))

(defthmd sub-func-real
  (realp (sub-func x)))

(defthmd sub-func-prime-real
  (realp (sub-func-prime x)))

(defthmd i-small-*-lemma
  (implies (and (i-small x)
                (i-small y))
           (i-small (* x y))))

(defthmd i-small-x-*-limited-y
  (implies (and (i-limited z)
                (i-small (- x x1)))
           (i-small (* z (- x x1))))
  :hints (("goal"
           :use (:instance limited*small->small (y (- x x1)) (x z))
           )))

(defthmd i-close-x-y=>
  (implies (i-close x y)
           (i-small (- x y)))
  :hints (("goal"
           :in-theory (enable i-close)
           )))

(defthmd i-close-x-y=>x*x-c-to-x*y
  (implies (and (i-limited x)
                (i-close x y))
           (i-close (* x x) (* x y))))

(defthmd i-close-x-y=>x*x-c-to-y*y
  (implies (and (i-limited x)
                (i-close x y))
           (i-close (* x x) (* y y))))

(defthmd i-close-x-y=>1-x-c-to-1-y
  (implies (i-close x y)
           (i-close (- 1 x) (- 1 y)))
  :hints (("goal"
           :in-theory (enable i-close)
           )))

(defthmd root-close-lemma
  (implies (and (realp y1)
		(realp y2)
		(not (= (standard-part y1) (standard-part y2))))
	   (not (i-close y1 y2)))
  :hints (("goal"
	   :in-theory (enable i-close i-small)
	   )))

(defthmd root-close-lemma-1
  (implies (and (realp y1)
		(realp y2)
		(not (i-close y1 y2)))
	   (not (= (standard-part y1) (standard-part y2))))
  :hints (("goal"
	   :in-theory (enable i-close i-small)
	   )))

(defthmd root-close-lemma-2
  (implies (and (realp y1)
                (realp y2)
                (i-limited y1)
                (i-limited y2)
                (>= y1 0)
                (>= y2 0)
                (not (i-close y1 y2)))
           (not (= (* (standard-part y1) (standard-part y1)) (* (standard-part y2) (standard-part y2))))
           )
  :hints (("goal"
           :use ((:instance root-close-lemma-1 (y1 y1) (y2 y2))
                 (:instance ineq-lemma4 (x1 (standard-part y1)) (x2 (standard-part y2)))
                 (:instance ineq-lemma4 (x1 (standard-part y2)) (x2 (standard-part y1))))
           :in-theory nil
           )))

(defthmd square-is-standard
  (implies (and (i-limited y1)
                (realp y1))
           (equal (* (standard-part y1) (standard-part y1))
                  (standard-part (square y1))
                  )))

(defthmd root-close-lemma-3
  (implies (and (realp y1)
                (realp y2)
                (i-limited y1)
                (i-limited y2)
                (>= y1 0)
                (>= y2 0)
                (not (i-close y1 y2)))
           (not (= (standard-part (square y1)) (standard-part (square y2)))))

  :hints (("goal"
           :use ((:instance root-close-lemma-2 (y1 y1) (y2 y2))
                 (:instance square-is-standard (y1 y1))
                 (:instance square-is-standard (y1 y2)))
           :in-theory nil
           )))

(defthmd sqr-real-lemma
  (implies (realp x)
           (realp (square x))))

(defthmd root-close-lemma-6
  (implies (and (realp y1)
                (realp y2)
                (i-limited y1)
                (i-limited y2)
                (>= y1 0)
                (>= y2 0)
                (not (i-close y1 y2)))
           (not (i-close (square y1) (square y2))))
  :hints (("goal"
           :use ((:instance root-close-lemma-3 (y1 y1) (y2 y2))
                 (:instance root-close-lemma (y1 (square y1)) (y2 (square y2)))
                 (:instance sqr-real-lemma (x y1))
                 (:instance sqr-real-lemma (x y2)))
           )))

(defthmd sqrt-real-lemma
  (implies (realp x)
           (realp (acl2-sqrt x))))

(defthmd sqrt>=0-lemma
  (implies (and (i-limited x)
                (realp x))
           (>= (acl2-sqrt x) 0)))

(defthmd i-close-x1-x2=>root-close
  (implies (and (standardp x1)
                (realp x1)
                (realp x2)
                (>= x1 0)
                (>= x2 0)
                (i-close x1 x2))
           (i-close (acl2-sqrt x1) (acl2-sqrt x2)))
  :hints (("goal"
           :use ((:definition square)
                 (:instance standards-are-limited-forward (x x1))
                 (:instance i-close-limited-2 (y x1) (x x2))
                 (:instance sqrt-real-lemma (x x1))
                 (:instance sqrt-real-lemma (x x2))
                 (:instance limited-sqrt (x x1))
                 (:instance limited-sqrt (x x2))
                 (:instance sqrt>=0-lemma (x x1))
                 (:instance sqrt>=0-lemma (x x2))
                 (:instance root-close-lemma-6 (y1 (acl2-sqrt x1) ) (y2 (acl2-sqrt x2))))
           )))

(defthmd i-close-x-x1=>i-limited-x1
  (implies (and (standardp x)
                (acl2-numberp x)
                (i-close x x1))
           (i-limited x1))
  :hints (("goal"
           :use ((:instance i-close-limited (y x1) (x x)))
           )))

(defthmd inside-interval=>i-limited
  (implies (inside-interval-p x (sub-domain))
           (i-limited x))
  :hints (("goal"
           :use ((:instance limited-squeeze (a (/ 1 4)) (b (/ 1 2)) (x x)))
           :in-theory (enable interval-definition-theory)
           )))

(defthmd i-limited-1-x*x
  (implies (i-limited x)
           (i-limited (- 1 (* x x)))))

(defthmd i-limited-1-x
  (implies (i-limited x)
           (i-limited (+ -1 (- x)))))

(defthmd standardp-x*x
  (implies (standardp x)
           (standardp (* x x))))

(defthmd standard-1-*x*x
  (implies (standardp x)
           (standardp (- 1 (* x x)))))

(defthmd x-in-sub-domain=>x>=0
  (implies (and (realp x)
                (>= x (acl2-sqrt (/ 12 16))))
           (>= x 0)))

(defthmd sqrt-1-*x*x-close-to-1-*x1*x1
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
                (inside-interval-p x1 (sub-domain))
                (i-close x x1))
           (i-close (acl2-sqrt (- 1 (* x x))) (acl2-sqrt (- 1 (* x1 x1)))))
  :hints (("goal"
           :use ((:instance i-close-x1-x2=>root-close (x1 (- 1 (* x x))) (x2 (- 1 (* x1 x1))))
                 (:instance sub-func-range-3 (x x))
                 (:instance sub-func-range-3 (x x1))
                 (:instance i-close-x-y=>x*x-c-to-y*y (x x) (y x1))
                 (:instance i-close-x-y=>1-x-c-to-1-y (x (* x x)) (y (* x1 x1)))
                 (:instance i-close (x x) (y x1))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd small-if-<-small-lemma
  (implies (and (i-small x)
                (realp x)
                (realp y)
                (<= 0 y)
                (<= y x))
           (i-small y))
  :hints (("goal"
           :use ((:instance standard-part-squeeze
                            (x 0)
                            (y y)
                            (z x)))
           :in-theory (disable
                       small-<-non-small))))

(defthmd sqrt-1-*x*x-not-i-small-1
  (implies (and (standardp x)
                (realp x)
                (> x 0))
           (not (i-small x)))
  :hints (("goal"
           :in-theory (enable i-small)
           )))

(defthm-std sqrt-1-*x*x-not-i-small-2
  (implies (standardp x)
           (standardp (acl2-sqrt x))))

(defthmd sqrt-1-*x*x-not-i-small
  (implies (and (inside-interval-p x (sub-domain))
                (standardp x))
           (not (i-small (acl2-sqrt (- 1 (* x x))))))
  :hints (("goal"
           :use ((:instance standard-part-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3 (x x))
                 (:instance small-if-<-small-lemma (x (- 1 (* x x))) (y (/ 12 16)))
                 (:instance sqrt-1-*x*x-not-i-small-1 (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance sqrt-1-*x*x-not-i-small-2 (x (- 1 (* x x))))
                 (:instance standard-1-*x*x (x x))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sqrt-1-*x*x-not-i-small-x1
  (implies (and (inside-interval-p x (sub-domain))
                (inside-interval-p x1 (sub-domain))
                (i-close x x1)
                (standardp x))
           (not (i-small (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("goal"
           :use ((:instance i-close-small-2
                            (y (acl2-sqrt (- 1 (* x1 x1))))
                            (x (acl2-sqrt (- 1 (* x1 x1)))))
                 (:instance sqrt-1-*x*x-not-i-small)
                 (:instance sqrt-1-*x*x-close-to-1-*x1*x1)
                 )
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd i-close-/-lemma
    (implies (and (i-close x x1)
                  (not (i-small x))
                  (i-limited x)
                  (i-limited x1)
                  (not (i-small x1))
                  (not (equal x 0))
                  (not (equal x1 0)))
             (i-close (/ x) (/ x1)))
    :hints (("goal"
             :use ((:instance limited*small->small (y (- x1 x)) (x (/ (* x x1))))
                   (:instance i-small-uminus (x (- x x1)))
                   )
             :in-theory (enable i-close)
             )))
  )

(defthmd i-close-1/sqrt-x-1/sqrt-x1
  (implies (and (inside-interval-p x (sub-domain))
                (inside-interval-p x1 (sub-domain))
                (i-close x x1)
                (standardp x))
           (i-close (/ (acl2-sqrt (- 1 (* x x)))) (/ (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("goal"
           :use ((:instance i-close-/-lemma (x (acl2-sqrt (- 1 (* x x)))) (x1 (acl2-sqrt (- 1 (* x1 x1)))))
                 (:instance sqrt-1-*x*x-close-to-1-*x1*x1 (x x) (x1 x1))
                 (:instance sqrt-1-*x*x-not-i-small (x x))
                 (:instance sqrt-1-*x*x-not-i-small-x1 (x x) (x1 x1))
                 (:instance limited-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd i-close-x-x1=>xy-to-x1y
  (implies (and (i-close x x1)
                (i-limited y))
           (i-close (* x y) (* x1 y))))

(defthmd sub-func-prime-continuous-1
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
           (i-close (/ (- x) (acl2-sqrt (- 1 (* x x))))
                    (/ (- x) (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("goal"
           :use ((:instance i-close-x-x1=>xy-to-x1y
                            (y x)
                            (x1 (/ (acl2-sqrt (- 1 (* x1 x1)))))
                            (x (/ (acl2-sqrt (- 1 (* x x))))))
                 (:instance i-limited-udivide (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance limited-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 (:instance sqrt-1-*x*x-not-i-small)
                 (:instance i-close-1/sqrt-x-1/sqrt-x1)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sub-func-prime-continuous-2
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
           (i-close (/ (- x) (acl2-sqrt (- 1 (* x1 x1))))
                    (/ (- x1) (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("goal"
           :use ((:instance i-close-x-x1=>xy-to-x1y
                            (x (- x))
                            (x1 (- x1))
                            (y (/ (acl2-sqrt (- 1 (* x1 x1))))))
                 (:instance i-limited-udivide (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance limited-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 (:instance i-close-limited
                            (x (/ (acl2-sqrt (- 1 (* x x)))))
                            (y (/ (acl2-sqrt (- 1 (* x1 x1))))))
                 (:instance i-close-1/sqrt-x-1/sqrt-x1)
                 (:instance sqrt-1-*x*x-not-i-small)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sub-func-prime-continuous
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(i-close x x1)
		(inside-interval-p x1 (sub-domain)))
	   (i-close (sub-func-prime x)
		    (sub-func-prime x1)))
  :hints (("goal"
           :use ((:instance sub-func-prime-continuous-1)
                 (:instance sub-func-prime-continuous-2)
                 )
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd int-f-range-2
    (implies (and (realp x)
                  (<= x (acl2-sqrt (/ 15 16)))
                  (>= x (acl2-sqrt (/ 12 16))))
             (and (<= (* x x) (/ 15 16))
                  (>= (* x x) (/ 12 16))))
    :hints (("goal"
             :use ((:instance sub-func-range-1 (x x) (y (acl2-sqrt (/ 15 16))))
                   (:instance sub-func-range-1 (x (acl2-sqrt (/ 12 16))) (y x))
                   (:instance sqrt-sqrt (x (/ 15 16)))
                   (:instance sqrt-sqrt (x (/ 12 16)))
                   )
             :in-theory (disable sqrt-/ sqrt->-0 y-=-sqrt sqrt-<-y y->-sqrt sqrt->-y y-<-sqrt)
             )))
  )

(defthmd int-f-range-3
  (implies (and (realp x)
                (<= x (acl2-sqrt (/ 15 16)))
                (>= x (acl2-sqrt (/ 12 16))))
           (and (<= (- 1 (* x x)) (/ 1 4))
                (>= (- 1 (* x x)) (/ 1 16))))
  :hints (("goal"
           :use ((:instance int-f-range-2))
           :in-theory (disable sqrt-/ sqrt->-0 y-=-sqrt sqrt-<-y y->-sqrt sqrt->-y y-<-sqrt)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd sub-func-range-4
    (implies (realp x)
             (realp (acl2-sqrt x))))

  (defthmd int-f-sqrt-range
    (implies (and (realp x)
                  (<= x (acl2-sqrt (/ 15 16)))
                  (>= x (acl2-sqrt (/ 12 16))))
             (and (<= (/ 1 4) (acl2-sqrt (- 1 (* x x))))
                  (<= (acl2-sqrt (- 1 (* x x))) (/ 1 2))))
    :hints (("goal"
             :use ((:instance sqrt-<-y (x (- 1 (* x x))) (y 1/2))
                   (:instance sqrt-<-y (x (- 1 (* x x))) (y 1/4))
                   (:instance int-f-range-3 (x x))
                   (:instance sub-func-range-4 (x (/ 15 16)))
                   (:instance sub-func-range-4 (x (/ 12 16)))
                   (:instance y-=-sqrt (x (- 1 (* x x))) (y 1/4))
                   (:instance y-=-sqrt (x (- 1 (* x x))) (y 1/2))
                   )
             )))
  )

(defthmd int-f-deno-range-1
  (implies (and (realp x)
                (<= x (acl2-sqrt (/ 15 16)))
                (>= x (acl2-sqrt (/ 12 16))))
           (<= (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))) 3/4))
  :hints (("goal"
           :use ((:instance int-f-range-3 (x x))
                 (:instance int-f-sqrt-range (x x))
                 )
           )))

(defthmd int-f-deno-range-2
  (implies (and (realp x)
                (<= x (acl2-sqrt (/ 15 16)))
                (>= x (acl2-sqrt (/ 12 16))))
           (>= (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))) 5/16))
  :hints (("goal"
           :use ((:instance int-f-range-3 (x x))
                 (:instance int-f-sqrt-range (x x))
                 )
           )))

(defthmd int-f-deno-range
  (implies (and (realp x)
                (<= x (acl2-sqrt (/ 15 16)))
                (>= x (acl2-sqrt (/ 12 16))))
           (and (<= (/ (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x))))) 16/5)
                (>= (/ (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x))))) 4/3)))
  :hints (("goal"
           :use ((:instance int-f-deno-range-1)
                 (:instance int-f-deno-range-2))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd int-f-range-lemma
    (implies (and (realp x)
                  (> a 0)
                  (> b 0)
                  (realp a)
                  (realp b)
                  (<= a x)
                  (realp y)
                  (<= b y))
             (<= (* a b) (* x y))))
  )

(defthmd int-f-range-1-1
  (implies (realp x)
           (realp (/ (+ (+ 1 (- (* x x)))
                        (acl2-sqrt (+ 1 (- (* x x)))))))))

(defthmd int-f-range-1
  (implies (and (realp x)
                (<= x (acl2-sqrt (/ 15 16)))
                (>= x (acl2-sqrt (/ 12 16))))
           (<= (/ x (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))
               (* (acl2-sqrt 15/16) 16/5)))
  :hints (("goal"
           :use ((:instance int-f-range-lemma (a x)
                            (b (/ (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x))))))
                            (x (acl2-sqrt (/ 15 16)))
                            (y 16/5))
                 (:instance int-f-deno-range (x x))
                 (:instance sqrt->-0 (x 12/16))
                 (:instance sub-func-range-4 (x 15/16))
                 (:instance int-f-range-1-1)
                 )
           :in-theory nil
           )))

(defthmd int-f-range-1-2
  (implies (and (realp x)
                (<= x (acl2-sqrt (/ 15 16)))
                (>= x (acl2-sqrt (/ 12 16))))
           (>= (/ x (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))
               (* (acl2-sqrt 12/16) 4/3)))
  :hints (("goal"
           :use ((:instance int-f-range-lemma (x x)
                            (y (/ (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x))))))
                            (a (acl2-sqrt (/ 12 16)))
                            (b 4/3))
                 (:instance int-f-deno-range (x x))
                 (:instance sqrt->-0 (x 12/16))
                 (:instance sub-func-range-4 (x 12/16))
                 (:instance int-f-range-1-1)
                 )
           :in-theory nil
           )))

(defthmd int-f-range-1-3
  (implies (inside-interval-p x (int-f-domain))
	   (and (<= (integral-function x) (* (acl2-sqrt 15/16) 16/5))
                (>= (integral-function x) (* (acl2-sqrt 12/16) 4/3))))
  :hints (("goal"
           :use ((:instance int-f-range-1)
                 (:instance int-f-range-1-2)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd int-f-range-1-4
  (and (equal (* (acl2-sqrt 15/16) 16/5)
              (acl2-sqrt 48/5))
       (equal (* (acl2-sqrt 12/16) 4/3)
              (acl2-sqrt 4/3)))
  :hints (("goal"
           :use ((:instance sqrt-*-x-x (x 16/5))
                 (:instance sqrt-*-x-x (x 4/3))
                 (:instance sqrt-* (x 15/16) (y (* 16/5 16/5)))
                 (:instance sqrt-* (x 12/16) (y (* 4/3 4/3)))
                 )
           )))

(defthmd int-f-range
  (implies (inside-interval-p x (int-f-domain))
	   (and (<= (integral-function x) (acl2-sqrt 48/5))
                (>= (integral-function x) (acl2-sqrt 4/3))))
  :hints (("goal"
           :use ((:instance int-f-range-1-3)
                 (:instance int-f-range-1-4)
                 )
           :in-theory nil
           )))

(defthmd sqrt-1-*x*x-close-to-1-*x1*x1-int-f
  (implies (and (standardp x)
		(inside-interval-p x (int-f-domain))
                (inside-interval-p x1 (int-f-domain))
                (i-close x x1))
           (i-close (acl2-sqrt (- 1 (* x x))) (acl2-sqrt (- 1 (* x1 x1)))))
  :hints (("goal"
           :use ((:instance i-close-x1-x2=>root-close (x1 (- 1 (* x x))) (x2 (- 1 (* x1 x1))))
                 (:instance int-f-range-3 (x x))
                 (:instance int-f-range-3 (x x1))
                 (:instance i-close-x-y=>x*x-c-to-y*y (x x) (y x1))
                 (:instance i-close-x-y=>1-x-c-to-1-y (x (* x x)) (y (* x1 x1)))
                 (:instance i-close (x x) (y x1))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd i-close-int-f-lemma
  (implies (and (i-close x y)
                (i-close a b))
           (i-close (+ x a) (+ y b)))
  :hints (("goal"
           :in-theory (enable i-close i-small)
           )))

(defthmd i-close-int-f-deno
  (implies (and (standardp x)
		(inside-interval-p x (int-f-domain))
                (inside-interval-p x1 (int-f-domain))
                (i-close x x1))
           (i-close (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x))))
                    (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("goal"
           :use ((:instance i-close-int-f-lemma
                            (x (acl2-sqrt (- 1 (* x x))))
                            (y (acl2-sqrt (- 1 (* x1 x1))))
                            (a (- 1 (* x x)))
                            (b (- 1 (* x1 x1))))
                 (:instance i-close-x-y=>1-x-c-to-1-y
                            (x (* x x))
                            (y (* x1 x1)))
                 (:instance sqrt-1-*x*x-close-to-1-*x1*x1-int-f)
                 (:instance i-close-x-y=>x*x-c-to-y*y
                            (x x) (y x1))
                 )
           )))

(defthmd sqrt-1-*x*x-not-i-small-int-f
  (implies (and (inside-interval-p x (int-f-domain))
                (standardp x))
           (not (i-small (acl2-sqrt (- 1 (* x x))))))
  :hints (("goal"
           :use ((:instance standard-part-sqrt (x (- 1 (* x x))))
                 (:instance int-f-range-3 (x x))
                 (:instance small-if-<-small-lemma (x (- 1 (* x x))) (y (/ 1 16)))
                 (:instance sqrt-1-*x*x-not-i-small-1 (x (acl2-sqrt (- 1 (* x x)))))
                 (:instance sqrt-1-*x*x-not-i-small-2 (x (- 1 (* x x))))
                 (:instance standard-1-*x*x (x x))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sqrt-1-*x*x-not-i-small-x1-int-f
  (implies (and (inside-interval-p x (int-f-domain))
                (inside-interval-p x1 (int-f-domain))
                (i-close x x1)
                (standardp x))
           (not (i-small (acl2-sqrt (- 1 (* x1 x1))))))
  :hints (("goal"
           :use ((:instance i-close-small-2
                            (y (acl2-sqrt (- 1 (* x x))))
                            (x (acl2-sqrt (- 1 (* x1 x1)))))
                 (:instance sqrt-1-*x*x-not-i-small-int-f)
                 (:instance sqrt-1-*x*x-close-to-1-*x1*x1-int-f)
                 )
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd not-i-small-x+y
    (implies (and (not (i-small x))
                  (realp x)
                  (realp y)
                  (> x 0)
                  (> y 0)
                  (not (i-small y)))
             (not (i-small (+ x y))))
    :hints (("goal"
             :use ((:instance standard-part-<-2 (x 0) (y y))
                   (:instance standard-part-<-2 (x 0) (y x))
                   )
             :in-theory (enable i-small)
             )))
  )

(defthmd int-f-deno-not-i-small
  (implies (and (inside-interval-p x (int-f-domain))
                (standardp x))
           (not (i-small (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))))
  :hints (("goal"
           :use ((:instance not-i-small-x+y (x (- 1 (* x x))) (y (acl2-sqrt (- 1 (* x x)))))
                 (:instance int-f-range-3 (x x))
                 )
           :in-theory (enable interval-definition-theory i-small)
           )))

(defthmd int-f-deno-not-i-small-x1
  (implies (and (inside-interval-p x (int-f-domain))
                (inside-interval-p x1 (int-f-domain))
                (i-close x x1)
                (standardp x))
           (not (i-small (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1)))))))
  :hints (("goal"
           :use ((:instance i-close-small-2
                            (x (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1)))))
                            (y (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x))))))
                 (:instance int-f-deno-not-i-small)
                 (:instance i-close-int-f-deno)
                 )
           )))

(defthmd int-f-i-limited-/deno
  (implies (and (inside-interval-p x (int-f-domain))
                (standardp x))
           (i-limited (/ (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))))
  :hints (("goal"
           :use ((:instance int-f-deno-range (x x))
                 (:instance limited-squeeze (x (/ (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))) (a 4/3) (b 16/5))
                 )
           :in-theory (e/d (interval-definition-theory) (sqrt-/ sqrt->-0 y-=-sqrt sqrt-<-y y->-sqrt sqrt->-y y-<-sqrt acl2-sqrt))
           )))

(defthmd int-f-i-limited-/deno-x1
  (implies (and (inside-interval-p x (int-f-domain))
                (inside-interval-p x1 (int-f-domain))
                (i-close x x1)
                (standardp x))
           (i-limited (/ (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1)))))))
  :hints (("goal"
           :use ((:instance int-f-deno-range (x x1))
                 (:instance limited-squeeze (x (/ (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1)))))) (a 4/3) (b 16/5))
                 )
           :in-theory (e/d (interval-definition-theory) (sqrt-/ sqrt->-0 y-=-sqrt sqrt-<-y y->-sqrt sqrt->-y y-<-sqrt acl2-sqrt))
           )))

(defthmd int-f-i-close-/deno
  (implies (and (inside-interval-p x (int-f-domain))
                (inside-interval-p x1 (int-f-domain))
                (i-close x x1)
                (standardp x))
           (i-close (/ (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))
                    (/ (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1)))))))
  :hints (("goal"
           :use ((:instance i-close-int-f-deno)
                 (:instance i-close-/-lemma
                            (x (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))
                            (x1 (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1))))))
                 (:instance int-f-deno-not-i-small)
                 (:instance int-f-deno-not-i-small-x1)
                 (:instance int-f-deno-range-1)
                 (:instance int-f-deno-range-2)
                 (:instance int-f-deno-range-1 (x x1))
                 (:instance int-f-deno-range-2 (x x1))
                 (:instance limited-squeeze (x (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x))))) (a 5/16) (b 3/4))
                 )
           :in-theory (e/d (interval-definition-theory) (sqrt-/ sqrt->-0 y-=-sqrt sqrt-<-y y->-sqrt sqrt->-y y-<-sqrt acl2-sqrt))
           )))

(defthmd int-f-continuous-1
  (implies (and (standardp x)
		(inside-interval-p x (int-f-domain))
		(i-close x x1)
		(inside-interval-p x1 (int-f-domain)))
           (i-close (/ x (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))
                    (/ x (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1)))))))
  :hints (("goal"
           :use ((:instance i-close-x-x1=>xy-to-x1y
                            (y x)
                            (x1 (/ (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1))))))
                            (x (/ (+ (- 1 (* x x)) (acl2-sqrt (- 1 (* x x)))))))
                 (:instance int-f-i-close-/deno)
                 )
           )))

(defthmd int-f-continuous-2
  (implies (and (standardp x)
		(inside-interval-p x (int-f-domain))
		(i-close x x1)
		(inside-interval-p x1 (int-f-domain)))
           (i-close (/ x (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1)))))
                    (/ x1 (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1)))))))
  :hints (("goal"
           :use ((:instance i-close-x-x1=>xy-to-x1y
                            (x x)
                            (x1 x1)
                            (y (/ (+ (- 1 (* x1 x1)) (acl2-sqrt (- 1 (* x1 x1)))))))
                 (:instance int-f-i-limited-/deno-x1 (x x) (x1 x1))
                 )
           )))

(defthmd int-f-continuous
  (implies (and (standardp x)
		(inside-interval-p x (int-f-domain))
		(i-close x x1)
		(inside-interval-p x1 (int-f-domain)))
	   (i-close (integral-function x)
		    (integral-function x1)))
  :hints (("goal"
           :use ((:instance int-f-continuous-1)
                 (:instance int-f-continuous-2)
                 )
           )))

(defthmd sqrt-1-x**2-derivative-1
  (equal (+ (- (* 1/2
                  x (/ (acl2-sqrt (+ 1 (- (* x x)))))))
            (- (* 1/2
                  x (/ (acl2-sqrt (+ 1 (- (* x x))))))))
         (- (* x (/ (acl2-sqrt (+ 1 (- (* x x)))))))))

(encapsulate
  ()
  (local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/sqrt-derivative" :dir :system))

  (defthmd sqrt-1-*x*x-not-i-small-100
    (implies (standardp x)
             (standardp (acl2-sqrt x))))

  (local
   (defderivative sqrt-1-x**2-derivative-lemma
     (acl2-sqrt (- 1 (* x x))))
   )

  (defthmd sqrt-1-x**2-derivative
    (implies (and (inside-interval-p x (sub-domain))
                  (inside-interval-p y (sub-domain))
                  (standardp x)
                  (i-close x y)
                  (not (equal x y)))
             (i-close (/ (- (acl2-sqrt (- 1 (* x x)))
                            (acl2-sqrt (- 1 (* y y))))
                         (- x y))
                      (/ (- x) (acl2-sqrt (- 1 (* x x))))))
    :hints (("goal"
             :use ((:instance sqrt-1-x**2-derivative-lemma)
                   (:instance sqrt-1-x**2-derivative-1)
                   (:instance sub-func-range-3 (x y))
                   (:instance sub-func-range-3 (x x)))
             :in-theory (enable interval-definition-theory)
             )))
  )

(defthmd sub-func-prime-is-derivative
  (implies (and (inside-interval-p x (sub-domain))
                (inside-interval-p y1 (sub-domain))
                (standardp x)
                (i-close x y1)
                (not (equal x y1)))
           (i-close (/ (- (sub-func x) (sub-func y1)) (- x y1))
                    (sub-func-prime x)))
  :hints (("goal"
           :use ((:instance sqrt-1-x**2-derivative (x x) (y y1))
                 )
           )))

(defthmd sub-func-differentiable-1
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(inside-interval-p y1 (sub-domain))
		(inside-interval-p y2 (sub-domain))
		(i-close x y1) (not (= x y1))
		(i-close x y2) (not (= x y2)))
           (i-close (/ (- (sub-func x) (sub-func y1)) (- x y1))
                    (/ (- (sub-func x) (sub-func y2)) (- x y2))))
  :hints (("goal"
           :use ((:instance sub-func-prime-is-derivative (x x) (y1 y1))
                 (:instance sub-func-prime-is-derivative (x x) (y1 y2))
                 )
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd sub-func-prime-range-1
    (implies (and (realp x)
                  (> a 0)
                  (> b 0)
                  (realp a)
                  (realp b)
                  (<= x a)
                  (>= x b))
             (and (<= (- (/ 1 b)) (- (/ 1 x)))
                  (<= (- (/ 1 x)) (- (/ 1 a))))))
  )

(defthmd sub-func-prime-range-2
  (implies (and (realp x)
                (<= x (/ 1 2))
                (>= x (/ 1 4)))
           (and (<= (- (acl2-sqrt 16/12))  (/ (- (acl2-sqrt (- 1 (* x x))))))
                (<= (/ (- (acl2-sqrt (- 1 (* x x))))) (- (acl2-sqrt 16/15)))))
  :hints (("goal"
           :use ((:instance sub-func-prime-range-1
                            (x (acl2-sqrt (- 1 (* x x))))
                            (b (acl2-sqrt 12/16))
                            (a (acl2-sqrt 15/16)))
                 (:instance sub-func-range (x x))
                 )
           )))

(defthmd sub-func-prime-range-3
  (implies (and (realp x)
                (realp a)
                (realp y)
                (< y 0)
                (<= a x))
           (>= (* a y) (* x y))))

(defthmd sub-func-prime-range-4
  (implies (and (realp x)
                (realp y1)
                (realp y)
                (<= y1 y)
                (> x 0))
           (<= (* y1 x) (* x y))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd sub-func-prime-range-6
    (implies (and (<= a x)
                  (<= x y))
             (<= a y)))

  (defthmd sub-func-prime-range-5
    (implies (and (realp x)
                  (realp a1)
                  (realp a2)
                  (<= a1 x)
                  (<= x a2)
                  (> a1 0)
                  (realp y)
                  (realp b1)
                  (realp b2)
                  (< b2 0)
                  (<= b1 y)
                  (<= y b2)
                  (i-limited a1)
                  (i-limited b1)
                  (i-limited a2)
                  (i-limited b2)
                  )
             (and (<= (* x y) (* a1 b2))
                  (<= (* a2 b1) (* x y))
                  (i-limited (* x y))))
    :hints (("goal"
             :use ((:instance sub-func-prime-range-3 (x x) (y y) (a a1))
                   (:instance sub-func-prime-range-4 (y1 y) (x a1) (y b2))
                   (:instance sub-func-prime-range-6 (a (* x y)) (x (* a1 y)) (y (* a1 b2)))
                   (:instance sub-func-prime-range-3 (x a2) (a x) (y y))
                   (:instance sub-func-prime-range-4 (x a2) (y y) (y1 b1))
                   (:instance sub-func-prime-range-6 (a (* a2 b1)) (x (* a2 y)) (y (* x y)))
                   (:instance limited-squeeze (a (* a2 b1)) (x (* x y)) (b (* a1 b2)))
                   )
             )))
  )

(defthmd sub-func-prime-range-7
  (implies (and (realp x)
                (<= x (/ 1 2))
                (>= x (/ 1 4)))
           (and (<= (- (acl2-sqrt 16/12))  (/ (- (acl2-sqrt (- 1 (* x x))))))
                (<= (/ (- (acl2-sqrt (- 1 (* x x))))) (- (acl2-sqrt 16/15)))))
  :hints (("goal"
           :use ((:instance sub-func-prime-range-1
                            (x (acl2-sqrt (- 1 (* x x))))
                            (b (acl2-sqrt 12/16))
                            (a (acl2-sqrt 15/16)))
                 (:instance sub-func-range (x x))
                 )
           )))

(defthmd sub-func-prime-range
  (implies (and (realp x)
                (<= x (/ 1 2))
                (>= x (/ 1 4)))
           (i-limited (* x (/ (- (acl2-sqrt (- 1 (* x x))))))))
  :hints (("goal"
           :use ((:instance sub-func-prime-range-5
                            (a1 1/4)
                            (a2 1/2)
                            (x x)
                            (b1 (- (acl2-sqrt 16/12)))
                            (b2 (- (acl2-sqrt 16/15)))
                            (y (/ (- (acl2-sqrt (- 1 (* x x)))))))
                 (:instance sub-func-prime-range-7)
                 ))))

(defthmd sub-func-differentiable-2
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(inside-interval-p y1 (sub-domain))
		(i-close x y1) (not (= x y1)))
           (i-limited (/ (- (sub-func x) (sub-func y1)) (- x y1))))
  :hints (("goal"
           :use ((:instance i-close-limited-2
                            (x (/ (- (sub-func x) (sub-func y1)) (- x y1)))
                            (y (sub-func-prime x)))
                 (:instance sub-func-range (x x))
                 (:instance sub-func-prime-is-derivative)
                 (:instance sub-func-prime-range)
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd sub-func-differentiable
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(inside-interval-p y1 (sub-domain))
		(inside-interval-p y2 (sub-domain))
		(i-close x y1) (not (= x y1))
		(i-close x y2) (not (= x y2)))
           (and (i-limited (/ (- (sub-func x) (sub-func y1)) (- x y1)))
                (i-close (/ (- (sub-func x) (sub-func y1)) (- x y1))
                         (/ (- (sub-func x) (sub-func y2)) (- x y2)))))
  :hints (("goal"
           :use ((:instance sub-func-differentiable-2)
                 (:instance sub-func-differentiable-1)
                 )
           )))

(encapsulate
  (
   (consta1 () t)
   )

  (local
   (defun consta1()
     (acl2-sqrt 14/16)))

  (defthmd consta1-def
    (and (inside-interval-p (consta1) (int-f-domain))
         (standardp (consta1))
         )
    :hints (("goal"
             :in-theory (enable interval-definition-theory)
             )))
  )

(encapsulate
  (((int-f-sub-derivative *) => *))

  (local
   (defun int-f-sub-derivative (x)
     (* (integral-function (sub-func x)) (sub-func-prime x))
     ))

  (defthmd derivative-int-f-sub-definition
    (implies (inside-interval-p x (sub-domain))
             (equal (int-f-sub-derivative x)
                    (* (integral-function (sub-func x))
                       (sub-func-prime x))))
    :hints (("goal"
             :use (:functional-instance derivative-cr-f-o-fi-definition
                                        (fi-domain sub-domain)
                                        (f-prime integral-function)
                                        (fi sub-func)
                                        (fi-prime sub-func-prime)
                                        (fi-range int-f-domain)
                                        (derivative-cr-f-o-fi int-f-sub-derivative)
                                        (consta consta1)
                                        )
             )
            ("subgoal 9"
             :use (:instance subfunc-range-in-domain-of-int-f)
             )
            ("subgoal 6"
             :use (:instance sub-func-prime-continuous)
             )
            ("subgoal 5"
             :use (:instance sub-func-prime-is-derivative (x x) (y1 x1))
             )
            ("subgoal 4"
             :use (:instance int-f-continuous)
             )
            ("subgoal 3"
             :use (:instance consta1-def)
             )
            ("subgoal 2"
             :use (:instance consta1-def)
             )
            )
    )
  )

(defun int-f-sub-prime (x)
  (if (inside-interval-p x (sub-domain))
      (int-f-sub-derivative x)
    0)
  )

(defun map-int-f-sub-prime (p)
  (if (consp p)
      (cons (int-f-sub-prime (car p))
	    (map-int-f-sub-prime (cdr p)))
    nil))

(defun riemann-int-f-sub-prime (p)
  (dotprod (deltas p)
	   (map-int-f-sub-prime (cdr p))))

(encapsulate
  nil

  (local
   (defthmd limited-riemann-int-f-sub-prime-small-partition
     (implies (and (realp a) (standardp a)
                   (realp b) (standardp b)
                   (inside-interval-p a (sub-domain))
                   (inside-interval-p b (sub-domain))
                   (< a b))
              (standardp (standard-part (riemann-int-f-sub-prime (make-small-partition a b)))))
     :hints (("goal"
              :use (:functional-instance limited-riemann-f-o-fi-prime-small-partition
                                         (fi-domain sub-domain)
                                         (f-o-fi-prime int-f-sub-prime)
                                         (map-f-o-fi-prime map-int-f-sub-prime)
                                         (riemann-f-o-fi-prime riemann-int-f-sub-prime)
                                         (derivative-cr-f-o-fi int-f-sub-derivative)
                                         (fi-range int-f-domain)
                                         (consta  consta1)
                                         (f-prime integral-function)
                                         (fi sub-func)
                                         (fi-prime sub-func-prime)
                                         ))
             ("subgoal 9"
              :use (:instance derivative-int-f-sub-definition)
              )
             ("subgoal 8"
              :use (:instance subfunc-range-in-domain-of-int-f)
              )
             ("subgoal 5"
              :use (:instance sub-func-prime-continuous)
              )
             ("subgoal 4"
              :use (:instance sub-func-prime-is-derivative (x x) (y1 x1))
              )
             ("subgoal 3"
              :use (:instance int-f-continuous)
              )
             ("subgoal 2"
              :use (:instance consta1-def)
              )
             ("subgoal 1"
              :use (:instance consta1-def)
              )
             )
     ))

  (local (in-theory nil))
  (local (in-theory (enable limited-riemann-int-f-sub-prime-small-partition nsa-theory)))

  (defun-std strict-int-int-f-sub-prime (a b)
    (if (and (realp a)
             (realp b)
             (inside-interval-p a (sub-domain))
             (inside-interval-p b (sub-domain))
             (< a b))
        (standard-part (riemann-int-f-sub-prime (make-small-partition a b)))
      0))

  (defthmd strict-int-int-f-sub-prime-lemma
    (implies
     (and (standardp a) (standardp b))
     (equal
      (strict-int-int-f-sub-prime a b)
      (if (and (realp a)
               (realp b)
               (inside-interval-p a (sub-domain))
               (inside-interval-p b (sub-domain))
               (< a b))
          (standard-part (riemann-int-f-sub-prime (make-small-partition a b)))
        0)))
    )
  )

(defun int-int-f-sub-prime (a b)
  (if (<= a b)
      (strict-int-int-f-sub-prime a b)
    (- (strict-int-int-f-sub-prime b a))))

(defun map-int-f (p)
  (if (consp p)
      (cons (integral-function (car p))
	    (map-int-f (cdr p)))
    nil))

(defun riemann-int-f (p)
  (dotprod (deltas p)
	   (map-int-f (cdr p))))


(encapsulate
  nil

  (local
   (defthmd limited-riemann-int-f-small-partition
     (implies (and (realp a) (standardp a)
                   (realp b) (standardp b)
                   (inside-interval-p a (int-f-domain))
                   (inside-interval-p b (int-f-domain))
                   (< a b))
              (standardp (standard-part (riemann-int-f (make-small-partition a b)))))
     :hints (("goal"
              :use (:functional-instance limited-riemann-f-prime-small-partition
                                         (fi-range int-f-domain)
                                         (f-prime integral-function)
                                         (map-f-prime map-int-f)
                                         (riemann-f-prime riemann-int-f)
                                         (fi-domain sub-domain)
                                         (fi sub-func)
                                         (fi-prime sub-func-prime)
                                         (consta consta1))
              )
             ("subgoal 2"
              :use (:instance riemann-int-f)
              )
             ("subgoal 1"
              :use (:instance  map-int-f)
              )

             )
     )
   )

  (local (in-theory nil))
  (local (in-theory (enable limited-riemann-int-f-small-partition nsa-theory)))

  (defun-std strict-int-int-f (a b)
    (if (and (realp a)
             (realp b)
             (inside-interval-p a (int-f-domain))
             (inside-interval-p b (int-f-domain))
             (< a b))
        (standard-part (riemann-int-f (make-small-partition a b)))
      0))

  (defthmd strict-int-int-f-lemma
    (implies
     (and (standardp a) (standardp b))
     (equal (strict-int-int-f a b)
            (if (and (realp a)
                     (realp b)
                     (inside-interval-p a (int-f-domain))
                     (inside-interval-p b (int-f-domain))
                     (< a b))
                (standard-part (riemann-int-f (make-small-partition a b)))
              0)))
    )
  )

(defun int-int-f (a b)
  (if (<= a b)
      (strict-int-int-f a b)
    (- (strict-int-int-f b a))))

(defthmd usubstitution-int-f
  (implies (and (inside-interval-p a (sub-domain))
		(inside-interval-p b (sub-domain)))
	   (equal (int-int-f (sub-func a) (sub-func b))
		  (int-int-f-sub-prime a b)))
  :hints (("goal"
	   :use (:functional-instance usubstitution-f-o-fi
				      (int-f-prime int-int-f)
				      (int-f-o-fi-prime int-int-f-sub-prime)
				      (fi-domain sub-domain)
				      (fi sub-func)
				      (fi-prime sub-func-prime)
				      (f-prime integral-function)
				      (consta consta1)
				      (fi-range int-f-domain)
				      (strict-int-f-o-fi-prime strict-int-int-f-sub-prime)
				      (strict-int-f-prime strict-int-int-f)
				      (riemann-f-o-fi-prime riemann-int-f-sub-prime)
				      (map-f-o-fi-prime map-int-f-sub-prime)
				      (map-f-prime map-int-f)
				      (riemann-f-prime riemann-int-f)
				      (f-o-fi-prime int-f-sub-prime)
				      (derivative-cr-f-o-fi int-f-sub-derivative)
				      )
	   )))

(encapsulate
  ()

  (local
   (defthm strict-int-rcdfn-prime-a-a-int-f
     (implies (inside-interval-p a (int-f-domain))
              (equal (strict-int-int-f a a) 0))
     :hints (("goal"
              :by (:functional-instance strict-int-a-a
                                        (strict-int-rcfn strict-int-int-f)
                                        (rcfn-domain int-f-domain)
                                        (rcfn integral-function)
                                        (riemann-rcfn riemann-int-f)
                                        (map-rcfn map-int-f)))
             ("subgoal 4"
              :use (:instance int-f-continuous (x x) (x1 y))
              )
             )
     ))

  (defthmd integral-reverse-interval-int-f
    (implies (and (realp a)
                  (realp b)
                  (inside-interval-p a (int-f-domain))
                  (inside-interval-p b (int-f-domain)))
             (equal (- (int-int-f a b))
                    (int-int-f b a))))
  )

(defthmd u-substitution-int-f-1
  (equal (int-int-f (acl2-sqrt 15/16) (acl2-sqrt 12/16))
         (int-int-f-sub-prime 1/4 1/2))
  :hints (("goal"
           :use ((:instance usubstitution-int-f (a 1/4) (b 1/2))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(defthmd u-substitution-int-f-2
  (equal (int-int-f (acl2-sqrt 12/16) (acl2-sqrt 15/16))
         (- (int-int-f-sub-prime 1/4 1/2)))
  :hints (("goal"
           :use ((:instance u-substitution-int-f-1)
                 (:instance integral-reverse-interval-int-f
                            (b (acl2-sqrt 12/16))
                            (a (acl2-sqrt 15/16)))
                 )
           :in-theory (enable interval-definition-theory)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd int-int-f-sub-prime-equals-1
    (implies (and (realp x)
                  (> x 0))
             (equal (- (* x (/ (+ x (* x x)))))
                    (- (/ (+ x 1))))))
  )

(defthmd int-int-f-sub-prime-equals
  (implies (inside-interval-p x (sub-domain))
           (equal (int-f-sub-prime x) (- (/ (+ x 1)))))
  :hints (("goal"
           :in-theory (enable interval-definition-theory)
           :use ((:instance derivative-int-f-sub-definition)
                 (:instance sub-func-range)
                 (:instance sqrt-sqrt (x (- 1 (* x x))))
                 (:instance sub-func-range-3)
                 (:instance int-int-f-sub-prime-equals-1)
                 ))))

(encapsulate
  ()
  (local (include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/ln-derivative-real" :dir :system))

  (local
   (defderivative ln-x+1-derivative-lemma
     (- (acl2-ln (+ x 1)))))

  (defthmd ln-x+1-derivative
    (implies (and (inside-interval-p x (sub-domain))
                  (inside-interval-p y (sub-domain))
                  (standardp x)
                  (i-close x y)
                  (not (equal x y)))
             (i-close (+ (- (* (acl2-ln (+ 1 x)) (/ (+ x (- y)))))
                         (* (acl2-ln (+ 1 y)) (/ (+ x (- y)))))
                      (- (/ (+ 1 x)))))
    :hints (("goal"
             :use ((:instance ln-x+1-derivative-lemma))
             :in-theory (enable interval-definition-theory)
             )))
  )

(defun minus-ln-x+1 (x)
  (if (inside-interval-p x (sub-domain))
      (- (acl2-ln (+ x 1)))
    0))

(defthmd minus-ln-x+1-is-derivative
  (implies (and (standardp x)
		(inside-interval-p x (sub-domain))
		(inside-interval-p x1 (sub-domain))
		(i-close x x1) (not (= x x1)))
	   (i-close (/ (- (minus-ln-x+1 x) (minus-ln-x+1 x1)) (- x x1))
		    (int-f-sub-prime x)))
  :hints (("goal"
           :use ((:instance ln-x+1-derivative (x x) (y x1))
                 (:instance int-int-f-sub-prime-equals)
                 )
           )))

(defthmd int-f-sub-prime-continuous-1
  (implies (i-close x x1)
           (i-close (- x) (- x1)))
  :hints (("goal"
           :in-theory (enable i-close)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd int-f-sub-prime-continuous-2
    (implies (realp x)
             (equal (/ (- x)) (- (/ x)))))

  (defthmd int-f-sub-prime-continuous-3
    (implies (realp x)
             (equal (/ (+ -1 (- x))) (- (/ (+ 1 x)))))
    :hints (("goal"
             :use (:instance int-f-sub-prime-continuous-2 (x (+ 1 x)))
             )))
  )

(defthmd int-f-sub-prime-continuous-5
  (implies (and (realp x)
                (inside-interval-p x (sub-domain))
                (inside-interval-p x1 (sub-domain))
                (i-close (/ (+ -1 (- x)))
                         (/ (+ -1 (- x1)))))
           (i-close (int-f-sub-prime x)
                    (int-f-sub-prime x1)))
  :hints (("goal"
           :use ((:instance int-int-f-sub-prime-equals (x x))
                 (:instance int-int-f-sub-prime-equals (x x1))
                 (:instance int-f-sub-prime-continuous-3 (x x))
                 (:instance int-f-sub-prime-continuous-3 (x x1))
                 )
           :in-theory (disable int-int-f-sub-prime)
           )))

(defthmd int-f-sub-prime-continuous
  (implies (and (standardp x)
                (inside-interval-p x (sub-domain))
                (i-close x x1)
                (inside-interval-p x1 (sub-domain)))
           (i-close (int-f-sub-prime x)
                    (int-f-sub-prime x1)))
  :hints (("goal"
           :use ((:instance int-int-f-sub-prime-equals)
                 (:instance int-int-f-sub-prime-equals (x x1))
                 (:instance i-close-/-lemma (x (- (+ 1 x))) (x1 (- (+ 1 x1))))
                 (:instance i-close-x-y=>1-x-c-to-1-y (x (- x)) (y (- x1)))
                 (:instance int-f-sub-prime-continuous-1 (x (+ 1 x)) (x1 (+ 1 x1)))
                 (:instance int-f-sub-prime-continuous-2 (x (+ 1 x)))
                 (:instance int-f-sub-prime-continuous-2 (x (+ 1 x1)))
                 (:instance int-f-sub-prime-continuous-3 (x x))
                 (:instance int-f-sub-prime-continuous-3 (x x1))
                 (:instance int-f-sub-prime-continuous-5 (x x) (x1 x1))
                 (:instance small-if-<-small (x (+ -1 (- x1))) (y 1/4))
                 (:instance i-close-limited (x (+ -1 (- x))) (y (+ -1 (- x1))))
                 (:instance i-limited-1-x)
                 (:instance i-close-limited (x (+ -1 (- x))) (y (+ -1 (- x1))))
                 )
           :in-theory (e/d (interval-definition-theory) (int-f-sub-prime))
           )))

(defthmd int-int-f-ftc-2
  (implies (and (inside-interval-p a (sub-domain))
		(inside-interval-p b (sub-domain)))
	   (equal (int-int-f-sub-prime a b)
		  (- (minus-ln-x+1 b)
		     (minus-ln-x+1 a))))
  :hints (("goal"
	   :use (:functional-instance ftc-2
				      (rcdfn minus-ln-x+1)
				      (rcdfn-prime int-f-sub-prime)
				      (map-rcdfn-prime map-int-f-sub-prime)
				      (riemann-rcdfn-prime riemann-int-f-sub-prime)
				      (rcdfn-domain sub-domain)
				      (int-rcdfn-prime int-int-f-sub-prime)
				      (strict-int-rcdfn-prime strict-int-int-f-sub-prime)
				      )
           :in-theory (disable int-f-sub-prime)
	   )
	  ("subgoal 9"
	   :use (:instance int-f-sub-prime-continuous)
	   )
	  ("subgoal 8"
	   :use (:instance minus-ln-x+1-is-derivative)
	   )
          ("subgoal 7"
           :use (:instance int-int-f-sub-prime-equals)
           :in-theory (enable interval-definition-theory)
           )
          ("subgoal 6"
           :use (:instance int-int-f-sub-prime-equals)
           :in-theory (enable interval-definition-theory)
           )
	  )
  )


(defthmd integral-function-value
  (equal (int-int-f (acl2-sqrt 12/16) (acl2-sqrt 15/16))
         (- (acl2-ln 3/2)
            (acl2-ln 5/4)))
  :hints (("goal"
           :use ((:instance u-substitution-int-f-2)
                 (:instance int-int-f-ftc-2 (a 1/4) (b 1/2))
                 )
           :in-theory (e/d (interval-definition-theory) (int-int-f int-int-f-sub-prime))
           )))
