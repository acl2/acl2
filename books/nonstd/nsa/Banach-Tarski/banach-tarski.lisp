; Banach-Tarski Theorem
;
; Proof of the Banach-Tarski theorem on the unit ball.
;
;
; Copyright (C) 2022 University of Wyoming
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Main Author: Jagadish Bapanapally (jagadishb285@gmail.com)
;
; Contributing Author:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(include-book "banach-tarski-b-0")

(defun vect-tr (x y z p)
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . ,(+ (aref2 :fake-name p 0 0) x) )
    ((1 . 0) . ,(+ (aref2 :fake-name p 1 0) y) )
    ((2 . 0) . ,(+ (aref2 :fake-name p 2 0) z) )
    ))

(defthmd vect-tr-values
  (and (equal (aref2 :fake-name (vect-tr x y z p) 0 0)
              (+ (aref2 :fake-name p 0 0) x))
       (equal (aref2 :fake-name (vect-tr x y z p) 1 0)
              (+ (aref2 :fake-name p 1 0) y))
       (equal (aref2 :fake-name (vect-tr x y z p) 2 0)
              (+ (aref2 :fake-name p 2 0) z)))
  :hints (("goal"
           :in-theory (enable aref2)
           )))

(defthmd r3p-vectr-tr-p
  (implies (and (point-in-r3 p)
                (realp x)
                (realp y)
                (realp z))
           (point-in-r3 (vect-tr x y z p)))
  :hints (("goal"
           :in-theory (enable array2p header dimensions aref2)
           )))

(defun return-point-in-r3 (x y z)
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . ,x )
    ((1 . 0) . ,y )
    ((2 . 0) . ,z )
    ))

(defthmd return-point-in-r3=>r3p
  (implies (and (realp x)
                (realp y)
                (realp z))
           (point-in-r3 (return-point-in-r3 x y z)))
  :hints (("goal"
           :in-theory (enable array2p header dimensions aref2)
           )))

(defun rotation-about-arbitrary-line (angle m n p)
  (vect-tr (point-in-r3-x1 m) (point-in-r3-y1 m) (point-in-r3-z1 m)
           (m-* (rotation-3d angle
                             (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                 (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                 (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                (vect-tr (- (point-in-r3-x1 m)) (- (point-in-r3-y1 m)) (- (point-in-r3-z1 m)) p))))

(defthmd rotation-about-arbitrary-line=>
  (implies (and (point-in-r3 m)
                (point-in-r3 n)
                (point-in-r3 p)
                (not (m-= m n))
                (realp angle)
                (equal (+ (* (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                             (- (point-in-r3-x1 n) (point-in-r3-x1 m)))
                          (* (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                             (- (point-in-r3-y1 n) (point-in-r3-y1 m)))
                          (* (- (point-in-r3-z1 n) (point-in-r3-z1 m))
                             (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                       1))
           (equal (rotation-about-arbitrary-line angle m n p)
                  (vect-tr (point-in-r3-x1 m) (point-in-r3-y1 m) (point-in-r3-z1 m)
                           (m-* (rotation-3d angle
                                             (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                                 (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                                 (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                                (vect-tr (- (point-in-r3-x1 m)) (- (point-in-r3-y1 m)) (- (point-in-r3-z1 m)) p)))))
  :hints (("goal"
           :in-theory (disable rotation-3d vect-tr point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-* return-point-in-r3)
           )))

(defthmd vectr-tr-lemma1
  (implies (and (m-= p1 p2)
                (point-in-r3 p1)
                (point-in-r3 p2))
           (equal (vect-tr x y z p1)
                  (vect-tr x y z p2)))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd rotation-about-arbitrary-line=>1
  (implies (and (m-= p1 p2)
                (point-in-r3 p1)
                (point-in-r3 p2))
           (equal (rotation-about-arbitrary-line angle m n p1)
                  (rotation-about-arbitrary-line angle m n p2)))
  :hints (("goal"
           :use ((:instance vectr-tr-lemma1 (p1 p1) (p2 p2)
                            (x (- (point-in-r3-x1 m)))
                            (y (- (point-in-r3-y1 m)))
                            (z (- (point-in-r3-z1 m)))))
           :in-theory (disable point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 return-point-in-r3
                               rotation-3d vect-tr m-*)
           )))

(defthmd rotation-about-arbitrary-line=>r3p
  (implies (and (point-in-r3 m)
                (point-in-r3 n)
                (point-in-r3 p)
                (realp angle))
           (point-in-r3 (rotation-about-arbitrary-line angle m n p)))
  :hints (("goal"
           :use ((:instance r3p-vectr-tr-p
                            (p (m-* (rotation-3d angle
                                                 (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                                     (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                                     (- (point-in-r3-z1 n) (point-in-r3-z1 m))))
                                    (vect-tr (- (point-in-r3-x1 m)) (- (point-in-r3-y1 m)) (- (point-in-r3-z1 m))
                                             p)))
                            (x (point-in-r3-x1 m))
                            (y (point-in-r3-y1 m))
                            (z (point-in-r3-z1 m)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (rot (rotation-3d angle
                                              (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                                  (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                                  (- (point-in-r3-z1 n) (point-in-r3-z1 m)))))
                            (p1 (vect-tr (- (point-in-r3-x1 m)) (- (point-in-r3-y1 m)) (- (point-in-r3-z1 m))
                                         p)))
                 (:instance r3-matrixp-r3d
                            (angle angle)
                            (u (return-point-in-r3 (- (point-in-r3-x1 n) (point-in-r3-x1 m))
                                                   (- (point-in-r3-y1 n) (point-in-r3-y1 m))
                                                   (- (point-in-r3-z1 n) (point-in-r3-z1 m)))))
                 (:instance r3p-vectr-tr-p
                            (p p)
                            (x (- (point-in-r3-x1 m)))
                            (y (- (point-in-r3-y1 m)))
                            (z (- (point-in-r3-z1 m))))
                 (:instance r3-rotationp-r-theta-11-1-lemma4
                            (p p))
                 (:instance r3-rotationp-r-theta-11-1-lemma4
                            (p m))
                 (:instance r3-rotationp-r-theta-11-1-lemma4
                            (p n))
                 (:instance return-point-in-r3=>r3p
                            (x (+ (point-in-r3-x1 n)
                                  (- (point-in-r3-x1 m))))
                            (y (+ (point-in-r3-y1 n)
                                  (- (point-in-r3-y1 m))))
                            (z (+ (point-in-r3-z1 n)
                                  (- (point-in-r3-z1 m)))))
                 (:instance rotation-about-arbitrary-line
                            (p p)
                            (m m)
                            (n n)
                            (angle angle))
                 )
           :in-theory nil
           )))

(defun m-p ()
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . 1/10)
    ((1 . 0) . 1/4)
    ((2 . 0) . 0)
    ))


(defun n-p ()
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . 11/10)
    ((1 . 0) . 1/4)
    ((2 . 0) . 0)
    ))

(defthmd return-point-in-r3-n-m=
  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
         `((:header :dimensions (3 1)
                    :maximum-length 15)
           ((0 . 0) . 1)
           ((1 . 0) . 0)
           ((2 . 0) . 0)
           ))
  :hints (("goal"
           :in-theory (enable aref2 )
           )))

(defthmd rotation-3d-angle-n-m=
  (implies (and (realp angle)
                (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                       ret-point))
           (equal (rotation-3d angle ret-point)
                  `((:header :dimensions (3 3)
                             :maximum-length 10)
                    ((0 . 0) . 1)
                    ((0 . 1) . 0)
                    ((0 . 2) . 0)
                    ((1 . 0) . 0)
                    ((1 . 1) . ,(acl2-cosine angle) )
                    ((1 . 2) . ,(- (acl2-sine angle)) )
                    ((2 . 0) . 0)
                    ((2 . 1) . ,(acl2-sine angle) )
                    ((2 . 2) . ,(acl2-cosine angle) )
                    )
                  )
           )
  )

(defthmd rotation-3d-angle-n-m=1
  (implies (and (realp angle)
                (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                       ret-point))
           (and (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 0) 1)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 0) 0)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 0) 0)
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))))
  :hints (("goal"
           :use ((:instance rotation-3d-angle-n-m= (angle angle) (ret-point ret-point))
                 )
           :in-theory (e/d (aref2) (rotation-3d))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd r3-rotationp-rotation-3d-angle-n-m-det
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point))
             (equal (r3-m-determinant (rotation-3d angle ret-point)) 1))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance rotation-3d-angle-n-m=1 (angle angle) (ret-point ret-point))
                   (:instance sin**2+cos**2 (x angle))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthm r3-rotationp-rotation-3d-angle-n-m-is-rot-sub9
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 0) 1)
                  (equal r3-m-rot-0-0
                         (/ (- (* (aref2 :fakename (rotation-3d angle ret-point) 1 1)
                                  (aref2 :fakename (rotation-3d angle ret-point) 2 2))
                               (* (aref2 :fakename (rotation-3d angle ret-point) 2 1)
                                  (aref2 :fakename (rotation-3d angle ret-point) 1 2)))
                            (r3-m-determinant (rotation-3d angle ret-point)))))
             (equal r3-m-rot-0-0
                    (aref2 :fake-name (m-trans (rotation-3d angle ret-point)) 0 0)))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-rotation-3d-angle-n-m-det
                              (angle angle)
                              (ret-point ret-point))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1 r3-m-determinant
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2
                                 m-p n-p r3-matrixp
                                 (:executable-counterpart m-p)
                                 (:executable-counterpart n-p)
                                 (:executable-counterpart point-in-r3)
                                 (:executable-counterpart point-in-r3-x1)
                                 (:executable-counterpart point-in-r3-y1)
                                 (:executable-counterpart point-in-r3-z1)
                                 (:executable-counterpart return-point-in-r3))
             ))
    :rule-classes nil)

  (defthm r3-rotationp-rotation-3d-angle-n-m-is-rot-sub8
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 0) 0)
                  (equal r3-m-rot-0-1
                         (/ (- (* (aref2 :fakename (rotation-3d angle ret-point) 0 2)
                                  (aref2 :fakename (rotation-3d angle ret-point) 2 1))
                               (* (aref2 :fakename (rotation-3d angle ret-point) 2 2)
                                  (aref2 :fakename (rotation-3d angle ret-point) 0 1)))
                            (r3-m-determinant (rotation-3d angle ret-point)))))
             (equal r3-m-rot-0-1
                    (aref2 :fake-name (m-trans (rotation-3d angle ret-point)) 0 1)))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-rotation-3d-angle-n-m-det
                              (angle angle)
                              (ret-point ret-point))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1 r3-m-determinant
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2
                                 m-p n-p r3-matrixp
                                 (:executable-counterpart m-p)
                                 (:executable-counterpart n-p)
                                 (:executable-counterpart point-in-r3)
                                 (:executable-counterpart point-in-r3-x1)
                                 (:executable-counterpart point-in-r3-y1)
                                 (:executable-counterpart point-in-r3-z1)
                                 (:executable-counterpart return-point-in-r3))
             ))
    :rule-classes nil)

  (defthm r3-rotationp-rotation-3d-angle-n-m-is-rot-sub7
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 0) 0)
                  (equal r3-m-rot-0-2
                         (/ (- (* (aref2 :fakename (rotation-3d angle ret-point) 0 1)
                                  (aref2 :fakename (rotation-3d angle ret-point) 1 2))
                               (* (aref2 :fakename (rotation-3d angle ret-point) 1 1)
                                  (aref2 :fakename (rotation-3d angle ret-point) 0 2)))
                            (r3-m-determinant (rotation-3d angle ret-point)))))
             (equal r3-m-rot-0-2
                    (aref2 :fake-name (m-trans (rotation-3d angle ret-point)) 0 2)))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-rotation-3d-angle-n-m-det
                              (angle angle)
                              (ret-point ret-point))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1 r3-m-determinant
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2
                                 m-p n-p r3-matrixp
                                 (:executable-counterpart m-p)
                                 (:executable-counterpart n-p)
                                 (:executable-counterpart point-in-r3)
                                 (:executable-counterpart point-in-r3-x1)
                                 (:executable-counterpart point-in-r3-y1)
                                 (:executable-counterpart point-in-r3-z1)
                                 (:executable-counterpart return-point-in-r3))
             ))
    :rule-classes nil)

  (defthm r3-rotationp-rotation-3d-angle-n-m-is-rot-sub6
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 0) 1)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))
                  (equal r3-m-rot-1-0
                         (/ (- (* (aref2 :fakename (rotation-3d angle ret-point) 1 2)
                                  (aref2 :fakename (rotation-3d angle ret-point) 2 0))
                               (* (aref2 :fakename (rotation-3d angle ret-point) 2 2)
                                  (aref2 :fakename (rotation-3d angle ret-point) 1 0)))
                            (r3-m-determinant (rotation-3d angle ret-point)))))
             (equal r3-m-rot-1-0
                    (aref2 :fake-name (m-trans (rotation-3d angle ret-point)) 1 0)))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-rotation-3d-angle-n-m-det
                              (angle angle)
                              (ret-point ret-point))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1 r3-m-determinant
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2
                                 m-p n-p r3-matrixp
                                 (:executable-counterpart m-p)
                                 (:executable-counterpart n-p)
                                 (:executable-counterpart point-in-r3)
                                 (:executable-counterpart point-in-r3-x1)
                                 (:executable-counterpart point-in-r3-y1)
                                 (:executable-counterpart point-in-r3-z1)
                                 (:executable-counterpart return-point-in-r3))
             ))
    :rule-classes nil)

  (defthm r3-rotationp-rotation-3d-angle-n-m-is-rot-sub5
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 0) 1)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))
                  (equal r3-m-rot-1-1
                         (/ (- (* (aref2 :fakename (rotation-3d angle ret-point) 0 0)
                                  (aref2 :fakename (rotation-3d angle ret-point) 2 2))
                               (* (aref2 :fakename (rotation-3d angle ret-point) 2 0)
                                  (aref2 :fakename (rotation-3d angle ret-point) 0 2)))
                            (r3-m-determinant (rotation-3d angle ret-point)))))
             (equal r3-m-rot-1-1
                    (aref2 :fake-name (m-trans (rotation-3d angle ret-point)) 1 1)))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-rotation-3d-angle-n-m-det
                              (angle angle)
                              (ret-point ret-point))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1 r3-m-determinant
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2
                                 m-p n-p r3-matrixp
                                 (:executable-counterpart m-p)
                                 (:executable-counterpart n-p)
                                 (:executable-counterpart point-in-r3)
                                 (:executable-counterpart point-in-r3-x1)
                                 (:executable-counterpart point-in-r3-y1)
                                 (:executable-counterpart point-in-r3-z1)
                                 (:executable-counterpart return-point-in-r3))
             ))
    :rule-classes nil)

  (defthm r3-rotationp-rotation-3d-angle-n-m-is-rot-sub4
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 0) 1)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))
                  (equal r3-m-rot-1-2
                         (/ (- (* (aref2 :fakename (rotation-3d angle ret-point) 0 2)
                                  (aref2 :fakename (rotation-3d angle ret-point) 1 0))
                               (* (aref2 :fakename (rotation-3d angle ret-point) 1 2)
                                  (aref2 :fakename (rotation-3d angle ret-point) 0 0)))
                            (r3-m-determinant (rotation-3d angle ret-point)))))
             (equal r3-m-rot-1-2
                    (aref2 :fake-name (m-trans (rotation-3d angle ret-point)) 1 2)))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-rotation-3d-angle-n-m-det
                              (angle angle)
                              (ret-point ret-point))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1 r3-m-determinant
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2
                                 m-p n-p r3-matrixp
                                 (:executable-counterpart m-p)
                                 (:executable-counterpart n-p)
                                 (:executable-counterpart point-in-r3)
                                 (:executable-counterpart point-in-r3-x1)
                                 (:executable-counterpart point-in-r3-y1)
                                 (:executable-counterpart point-in-r3-z1)
                                 (:executable-counterpart return-point-in-r3))
             ))
    :rule-classes nil)

  (defthm r3-rotationp-rotation-3d-angle-n-m-is-rot-sub3
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 0) 1)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))
                  (equal r3-m-rot-2-0
                         (/ (- (* (aref2 :fakename (rotation-3d angle ret-point) 1 0)
                                  (aref2 :fakename (rotation-3d angle ret-point) 2 1))
                               (* (aref2 :fakename (rotation-3d angle ret-point) 2 0)
                                  (aref2 :fakename (rotation-3d angle ret-point) 1 1)))
                            (r3-m-determinant (rotation-3d angle ret-point)))))
             (equal r3-m-rot-2-0
                    (aref2 :fake-name (m-trans (rotation-3d angle ret-point)) 2 0)))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-rotation-3d-angle-n-m-det
                              (angle angle)
                              (ret-point ret-point))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1 r3-m-determinant
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2
                                 m-p n-p r3-matrixp
                                 (:executable-counterpart m-p)
                                 (:executable-counterpart n-p)
                                 (:executable-counterpart point-in-r3)
                                 (:executable-counterpart point-in-r3-x1)
                                 (:executable-counterpart point-in-r3-y1)
                                 (:executable-counterpart point-in-r3-z1)
                                 (:executable-counterpart return-point-in-r3))
             ))
    :rule-classes nil)

  (defthm r3-rotationp-rotation-3d-angle-n-m-is-rot-sub2
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 0) 1)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))
                  (equal r3-m-rot-2-1
                         (/ (- (* (aref2 :fakename (rotation-3d angle ret-point) 0 1)
                                  (aref2 :fakename (rotation-3d angle ret-point) 2 0))
                               (* (aref2 :fakename (rotation-3d angle ret-point) 2 1)
                                  (aref2 :fakename (rotation-3d angle ret-point) 0 0)))
                            (r3-m-determinant (rotation-3d angle ret-point)))))
             (equal r3-m-rot-2-1
                    (aref2 :fake-name (m-trans (rotation-3d angle ret-point)) 2 1)))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-rotation-3d-angle-n-m-det
                              (angle angle)
                              (ret-point ret-point))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1 r3-m-determinant
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2
                                 m-p n-p r3-matrixp
                                 (:executable-counterpart m-p)
                                 (:executable-counterpart n-p)
                                 (:executable-counterpart point-in-r3)
                                 (:executable-counterpart point-in-r3-x1)
                                 (:executable-counterpart point-in-r3-y1)
                                 (:executable-counterpart point-in-r3-z1)
                                 (:executable-counterpart return-point-in-r3))
             ))
    :rule-classes nil)

  (defthm r3-rotationp-rotation-3d-angle-n-m-is-rot-sub1
    (implies (and (realp angle)
                  (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                         ret-point)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 0) 1)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 1) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 0 2) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 1) (acl2-cosine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 1 2) (- (acl2-sine angle)))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 0) 0)
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 1) (acl2-sine angle))
                  (equal (aref2 :fake-name (rotation-3d angle ret-point) 2 2) (acl2-cosine angle))
                  (equal (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 2 2)
                         (/ (- (* (aref2 :fakename (rotation-3d angle ret-point) 0 0)
                                  (aref2 :fakename (rotation-3d angle ret-point) 1 1))
                               (* (aref2 :fakename (rotation-3d angle ret-point) 1 0)
                                  (aref2 :fakename (rotation-3d angle ret-point) 0 1)))
                            (r3-m-determinant (rotation-3d angle ret-point)))))
             (equal (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 2 2)
                    (aref2 :fake-name (m-trans (rotation-3d angle ret-point)) 2 2)))
    :hints (("goal"
             :use ((:instance r3-matrixp-r3d (angle angle)
                              (u ret-point))
                   (:instance return-point-in-r3-n-m=)
                   (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance r3-rotationp-rotation-3d-angle-n-m-det
                              (angle angle)
                              (ret-point ret-point))
                   )
             :in-theory (disable aref2 rotation-3d return-point-in-r3 point-in-r3-x1 r3-m-determinant
                                 point-in-r3-y1 point-in-r3-z1 point-in-r3 r3-m-inverse m-trans sin**2+cos**2
                                 m-p n-p r3-matrixp
                                 (:executable-counterpart m-p)
                                 (:executable-counterpart n-p)
                                 (:executable-counterpart point-in-r3)
                                 (:executable-counterpart point-in-r3-x1)
                                 (:executable-counterpart point-in-r3-y1)
                                 (:executable-counterpart point-in-r3-z1)
                                 (:executable-counterpart return-point-in-r3))
             ))
    :rule-classes nil)

  )

(defthmd r3-rotationp-rotation-3d-angle-n-m-is-rot-lemma1
  (implies (and (realp angle)
                (point-in-r3 (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                 (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                 (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p)))))
                (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                       ret-point))
           (and (r3-matrixp (rotation-3d angle ret-point))
                (equal (r3-m-determinant (rotation-3d angle ret-point)) 1)))
  :hints (("goal"
           :use ((:instance r3-matrixp-r3d (angle angle)
                            (u ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-det
                            (angle angle)
                            (ret-point ret-point))
                 )
           :in-theory nil
           )))

(defthmd r3-rotationp-rotation-3d-angle-n-m-is-rot-lemma2-1
  (and (equal
        (aref2
         :fake-name
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         2 2)
        (aref2
         :fakename
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         2 2))

       (equal
        (aref2
         :fake-name
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         0 0)
        (aref2
         :fakename
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         0 0))

       (equal
        (aref2
         :fake-name
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         0 1)
        (aref2
         :fakename
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         0 1))

       (equal
        (aref2
         :fake-name
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         0 2)
        (aref2
         :fakename
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         0 2))

       (equal
        (aref2
         :fake-name
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         1 0)
        (aref2
         :fakename
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         1 0))

       (equal
        (aref2
         :fake-name
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         1 1)
        (aref2
         :fakename
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         1 1))

       (equal
        (aref2
         :fake-name
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         1 2)
        (aref2
         :fakename
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         1 2))

       (equal
        (aref2
         :fake-name
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         2 0)
        (aref2
         :fakename
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         2 0))

       (equal
        (aref2
         :fake-name
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         2 1)
        (aref2
         :fakename
         (r3-m-inverse
          (rotation-3d angle
                       (return-point-in-r3 (+ (point-in-r3-x1 (n-p))
                                              (- (point-in-r3-x1 (m-p))))
                                           (+ (point-in-r3-y1 (n-p))
                                              (- (point-in-r3-y1 (m-p))))
                                           (+ (point-in-r3-z1 (n-p))
                                              (- (point-in-r3-z1 (m-p)))))))
         2 1))

       )
  )

(defthmd r3-rotationp-rotation-3d-angle-n-m-is-rot-lemma2
  (implies (and (realp angle)
                (point-in-r3 (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                 (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                 (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p)))))
                (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                       ret-point))
           (m-= (r3-m-inverse (rotation-3d angle ret-point))
                (m-trans (rotation-3d angle ret-point))))
  :hints (("goal"
           :use ((:instance r3-matrixp-r3d (angle angle)
                            (u ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-lemma2-1)
                 (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle ret-point)))
                 (:instance r3-matrixp-m-trans (m (rotation-3d angle ret-point)))
                 (:instance r3-m-inverse-= (m (rotation-3d angle ret-point)))
                 (:instance rotation-3d-angle-n-m=1 (angle angle) (ret-point ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-sub1
                            (angle angle) (ret-point (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                                         (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                                         (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-sub2
                            (r3-m-rot-2-1 (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 2 1))
                            (angle angle) (ret-point ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-sub3
                            (r3-m-rot-2-0 (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 2 0))
                            (angle angle) (ret-point ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-sub4
                            (r3-m-rot-1-2 (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 1 2))
                            (angle angle) (ret-point ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-sub5
                            (r3-m-rot-1-1 (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 1 1))
                            (angle angle) (ret-point ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-sub6
                            (r3-m-rot-1-0 (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 1 0))
                            (angle angle) (ret-point ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-sub7
                            (r3-m-rot-0-2 (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 0 2))
                            (angle angle) (ret-point ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-sub8
                            (r3-m-rot-0-1 (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 0 1))
                            (angle angle) (ret-point ret-point))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-sub9
                            (r3-m-rot-0-0 (aref2 :fake-name (r3-m-inverse (rotation-3d angle ret-point)) 0 0))
                            (angle angle) (ret-point ret-point))

                 (:instance m-=-equiv-lemma
                            (m1 (r3-m-inverse (rotation-3d angle ret-point)))
                            (m2 (m-trans (rotation-3d angle ret-point))))

                 )
           :in-theory nil)))

(defthmd r3-rotationp-rotation-3d-angle-n-m-is-rot
  (implies (realp angle)
           (r3-rotationp (rotation-3d angle (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                                (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                                (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p)))))))
  :hints (("goal"
           :use ((:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-lemma2
                            (angle angle)
                            (ret-point (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))))
                 (:instance r3-rotationp-rotation-3d-angle-n-m-is-rot-lemma1
                            (angle angle)
                            (ret-point (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))))
                 (:instance return-point-in-r3=>r3p
                            (x (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p))))
                            (y (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p))))
                            (z (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                            )

                 )
           :in-theory (disable rotation-3d r3-matrixp r3-m-determinant r3-m-inverse m-trans)
           )))

(defthmd m-*rot-3d-vect-tr-values-1
  (and (equal (aref2 :fake-name
                     (list '(:header :dimensions (3 1)
                                     :maximum-length 4
                                     :default 0
                                     :name matrix-product)
                           (cons '(2 . 0)
                                 (+ (* -1/4 (acl2-sine angle))
                                    (* 0 (aref2 :fake-name p 0 0))
                                    (* (acl2-sine angle)
                                       (aref2 :fake-name p 1 0))
                                    (* (acl2-cosine angle)
                                       (aref2 :fake-name p 2 0))))
                           (cons '(1 . 0)
                                 (+ (* -1/4 (acl2-cosine angle))
                                    (* 0 (aref2 :fake-name p 0 0))
                                    (* (acl2-cosine angle)
                                       (aref2 :fake-name p 1 0))
                                    (* (aref2 :fake-name p 2 0)
                                       (- (acl2-sine angle)))))
                           (cons '(0 . 0)
                                 (+ -1/10 (aref2 :fake-name p 0 0)
                                    (* 0 (aref2 :fake-name p 1 0))
                                    (* 0 (aref2 :fake-name p 2 0)))))
                     0 0)
              (+ -1/10 (aref2 :fake-name p 0 0)))
       (equal (aref2 :fake-name
                     (list '(:header :dimensions (3 1)
                                     :maximum-length 4
                                     :default 0
                                     :name matrix-product)
                           (cons '(2 . 0)
                                 (+ (* -1/4 (acl2-sine angle))
                                    (* 0 (aref2 :fake-name p 0 0))
                                    (* (acl2-sine angle)
                                       (aref2 :fake-name p 1 0))
                                    (* (acl2-cosine angle)
                                       (aref2 :fake-name p 2 0))))
                           (cons '(1 . 0)
                                 (+ (* -1/4 (acl2-cosine angle))
                                    (* 0 (aref2 :fake-name p 0 0))
                                    (* (acl2-cosine angle)
                                       (aref2 :fake-name p 1 0))
                                    (* (aref2 :fake-name p 2 0)
                                       (- (acl2-sine angle)))))
                           (cons '(0 . 0)
                                 (+ -1/10 (aref2 :fake-name p 0 0)
                                    (* 0 (aref2 :fake-name p 1 0))
                                    (* 0 (aref2 :fake-name p 2 0)))))
                     2 0)
              (+ (* -1/4 (acl2-sine angle))
                 (* (acl2-sine angle)
                    (aref2 :fake-name p 1 0))
                 (* (acl2-cosine angle)
                    (aref2 :fake-name p 2 0))))
       (equal (aref2 :fake-name
                     (list '(:header :dimensions (3 1)
                                     :maximum-length 4
                                     :default 0
                                     :name matrix-product)
                           (cons '(2 . 0)
                                 (+ (* -1/4 (acl2-sine angle))
                                    (* 0 (aref2 :fake-name p 0 0))
                                    (* (acl2-sine angle)
                                       (aref2 :fake-name p 1 0))
                                    (* (acl2-cosine angle)
                                       (aref2 :fake-name p 2 0))))
                           (cons '(1 . 0)
                                 (+ (* -1/4 (acl2-cosine angle))
                                    (* 0 (aref2 :fake-name p 0 0))
                                    (* (acl2-cosine angle)
                                       (aref2 :fake-name p 1 0))
                                    (* (aref2 :fake-name p 2 0)
                                       (- (acl2-sine angle)))))
                           (cons '(0 . 0)
                                 (+ -1/10 (aref2 :fake-name p 0 0)
                                    (* 0 (aref2 :fake-name p 1 0))
                                    (* 0 (aref2 :fake-name p 2 0)))))
                     1 0)
              (+ (* -1/4 (acl2-cosine angle))
                 (* (acl2-cosine angle)
                    (aref2 :fake-name p 1 0))
                 (* (aref2 :fake-name p 2 0)
                    (- (acl2-sine angle)))))
       )

  :hints (("goal"
           :in-theory (enable aref2)
           )))

(defthmd m-*rot-3d-vect-tr-values
  (implies (and (realp angle)
                (point-in-r3 p)
                (equal (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p))))
                       ret-point)
                (equal (vect-tr (- (point-in-r3-x1 (m-p))) (- (point-in-r3-y1 (m-p))) (- (point-in-r3-z1 (m-p))) p)
                       vectr-tr-to-z))
           (and (equal (aref2 :fake-name (m-* (rotation-3d angle ret-point) vectr-tr-to-z) 0 0)
                       (- (point-in-r3-x1 p) 1/10))
                (equal (aref2 :fake-name (m-* (rotation-3d angle ret-point) vectr-tr-to-z) 1 0)
                       (+ (* (acl2-cosine angle) (- (point-in-r3-y1 p) 1/4))
                          (* (- (acl2-sine angle)) (point-in-r3-z1 p))))
                (equal (aref2 :fake-name (m-* (rotation-3d angle ret-point) vectr-tr-to-z) 2 0)
                       (+ (* (acl2-sine angle) (- (point-in-r3-y1 p) 1/4))
                          (* (acl2-cosine angle) (point-in-r3-z1 p))))))
  :hints (("goal"
           :use ((:instance rotation-3d-angle-n-m=)
                 (:instance r3p-vectr-tr-p
                            (p p)
                            (x (- (point-in-r3-x1 (m-p))))
                            (y (- (point-in-r3-y1 (m-p))))
                            (z (- (point-in-r3-z1 (m-p)))))
                 (:instance r3-matrixp-r3d
                            (angle angle)
                            (u ret-point))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l vectr-tr-to-z))
                 (:instance vect-tr-values
                            (p p)
                            (x (- (point-in-r3-x1 (m-p))))
                            (y (- (point-in-r3-y1 (m-p))))
                            (z (- (point-in-r3-z1 (m-p)))))
                 (:instance rotation-3d-angle-n-m=1)
                 (:instance m-*rot-3d-vect-tr-values-1)
                 )
           :in-theory (e/d (m-*) (rotation-3d))
           )))

(defthmd vectr-tr-m-*rot-3d-vect-tr=
  (implies (and (realp angle)
                (point-in-r3 p))
           (equal (rotation-about-arbitrary-line angle (m-p) (n-p) p)
                  `((:header :dimensions (3 1)
                             :maximum-length 15)
                    ((0 . 0) . ,(point-in-r3-x1 p) )
                    ((1 . 0) . ,(+ (* (acl2-cosine angle) (- (point-in-r3-y1 p) 1/4))
                                   (* (- (acl2-sine angle)) (point-in-r3-z1 p))
                                   1/4) )
                    ((2 . 0) . ,(+ (* (acl2-sine angle) (- (point-in-r3-y1 p) 1/4))
                                   (* (acl2-cosine angle) (point-in-r3-z1 p))) )
                    )
                  ))
  :hints (("goal"
           :use ((:instance m-*rot-3d-vect-tr-values
                            (angle angle)
                            (p p)
                            (ret-point (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p)))))
                            (vectr-tr-to-z (vect-tr (- (point-in-r3-x1 (m-p)))
                                                    (- (point-in-r3-y1 (m-p)))
                                                    (- (point-in-r3-z1 (m-p))) p)))
                 (:instance vect-tr
                            (x 1/10)
                            (y 1/4)
                            (z 0)
                            (p (m-* (rotation-3d angle (return-point-in-r3 (- (point-in-r3-x1 (n-p)) (point-in-r3-x1 (m-p)))
                                                                           (- (point-in-r3-y1 (n-p)) (point-in-r3-y1 (m-p)))
                                                                           (- (point-in-r3-z1 (n-p)) (point-in-r3-z1 (m-p)))))
                                    (vect-tr (- (point-in-r3-x1 (m-p)))
                                             (- (point-in-r3-y1 (m-p)))
                                             (- (point-in-r3-z1 (m-p))) p))))
                 )
           :in-theory (disable m-* rotation-3d vect-tr)
           )))

(defthmd vectr-tr-m-*rot-3d-vect-tr-values
  (implies (and (realp angle)
                (point-in-r3 p))
           (and (equal (aref2 :fake-name (rotation-about-arbitrary-line angle (m-p) (n-p) p) 0 0)
                       (point-in-r3-x1 p))
                (equal (aref2 :fake-name (rotation-about-arbitrary-line angle (m-p) (n-p) p) 1 0)
                       (+ (* (acl2-cosine angle) (- (point-in-r3-y1 p) 1/4))
                          (* (- (acl2-sine angle)) (point-in-r3-z1 p))
                          1/4))
                (equal (aref2 :fake-name (rotation-about-arbitrary-line angle (m-p) (n-p) p) 2 0)
                       (+ (* (acl2-sine angle) (- (point-in-r3-y1 p) 1/4))
                          (* (acl2-cosine angle) (point-in-r3-z1 p))))))
  :hints (("goal"
           :use ((:instance vectr-tr-m-*rot-3d-vect-tr= (angle angle) (p p))
                 )
           :in-theory (e/d (aref2) (rotation-about-arbitrary-line))
           )))

(defthmd rotation-about-arbitrary-line=p
  (implies (and (equal angle 0)
                (point-in-r3 p))
           (m-= (rotation-about-arbitrary-line angle (m-p) (n-p) p) p))
  :hints (("goal"
           :use ((:instance vectr-tr-m-*rot-3d-vect-tr-values
                            (angle 0)
                            (p p))
                 (:instance rotation-about-arbitrary-line=>r3p
                            (m (m-p))
                            (n (n-p))
                            (p p)
                            (angle 0)))
           :in-theory (e/d (m-=) (rotation-about-arbitrary-line))
           )))

(defthmd m-=-equiv-lemma-pr3
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (equal (aref2 :fake-name p1 0 0) (aref2 :fake-name p2 0 0))
                (equal (aref2 :fake-name p1 1 0) (aref2 :fake-name p2 1 0))
                (equal (aref2 :fake-name p1 2 0) (aref2 :fake-name p2 2 0))
                )
           (m-= p1 p2))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd rot-angle1-of-angle2*p=>1
    (implies (and (realp x)
                  (realp y)
                  (realp z)
                  (realp angle1)
                  (realp angle2)
                  (equal y-of-ang2 (+ (* (acl2-cosine angle2)
                                         (+ -1/4 y))
                                      (* (- (acl2-sine angle2))
                                         z)
                                      1/4))
                  (equal z-of-ang2 (+ (* (acl2-sine angle2)
                                         (+ -1/4 y))
                                      (* (acl2-cosine angle2)
                                         z))))
             (equal (+ (* (acl2-cosine angle1)
                          (+ -1/4
                             y-of-ang2))
                       (* (- (acl2-sine angle1))
                          z-of-ang2)
                       1/4)
                    (+ (* (acl2-cosine (+ angle1 angle2))
                          (+ -1/4 y))
                       (* (- (acl2-sine (+ angle1 angle2)))
                          z)
                       1/4))))

  (defthmd rot-angle1-of-angle2*p=>2
    (implies (and (realp x)
                  (realp y)
                  (realp z)
                  (realp angle1)
                  (realp angle2)
                  (equal y-of-ang2 (+ (* (acl2-cosine angle2)
                                         (+ -1/4 y))
                                      (* (- (acl2-sine angle2))
                                         z)
                                      1/4))
                  (equal z-of-ang2 (+ (* (acl2-sine angle2)
                                         (+ -1/4 y))
                                      (* (acl2-cosine angle2)
                                         z))))
             (equal (+ (* (acl2-sine angle1)
                          (+ -1/4
                             y-of-ang2))
                       (* (acl2-cosine angle1)
                          z-of-ang2))
                    (+ (* (acl2-sine (+ angle1 angle2))
                          (+ -1/4 y))
                       (* (acl2-cosine (+ angle1 angle2))
                          z)))))
  )

(defthmd rot-angle1-of-angle2*p=>
  (implies (and (point-in-r3 p)
                (point-in-r3 (m-p))
                (point-in-r3 (n-p))
                (realp angle1)
                (realp angle2))
           (m-= (rotation-about-arbitrary-line
                 angle1 (m-p) (n-p)
                 (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))
                (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
  :hints (("goal"
           :use ((:instance vectr-tr-m-*rot-3d-vect-tr-values
                            (angle angle2)
                            (p p))
                 (:instance vectr-tr-m-*rot-3d-vect-tr-values
                            (angle angle1)
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance rotation-about-arbitrary-line=>r3p
                            (m (m-p))
                            (n (n-p))
                            (p p)
                            (angle angle2))
                 (:instance rotation-about-arbitrary-line=>r3p
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))
                            (angle angle1)
                            (m (m-p))
                            (n (n-p)))
                 (:instance vectr-tr-m-*rot-3d-vect-tr-values
                            (angle (+ angle1 angle2))
                            (p p))
                 (:instance rotation-about-arbitrary-line=>r3p
                            (p p)
                            (angle (+ angle1 angle2))
                            (m (m-p))
                            (n (n-p)))
                 (:instance r3-rotationp-r-theta-11-1-lemma4
                            (p p))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (rotation-about-arbitrary-line
                                angle1 (m-p) (n-p)
                                (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))))
                 (:instance point-in-r3
                            (x (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
                 (:instance point-in-r3
                            (x (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance point-in-r3
                            (x (rotation-about-arbitrary-line
                                angle1 (m-p) (n-p)
                                (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))))
                 (:instance point-in-r3-x1
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance point-in-r3-y1
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance point-in-r3-z1
                            (p (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                 (:instance m-=-equiv-lemma-pr3
                            (p1 (rotation-about-arbitrary-line
                                 angle1 (m-p) (n-p)
                                 (rotation-about-arbitrary-line angle2 (m-p) (n-p) p)))
                            (p2 (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
                 (:instance rot-angle1-of-angle2*p=>2
                            (x (point-in-r3-x1 p))
                            (y (point-in-r3-y1 p))
                            (z (point-in-r3-z1 p))
                            (angle1 angle1)
                            (angle2 angle2)
                            (y-of-ang2 (+ (* (acl2-cosine angle2)
                                             (+ -1/4 (point-in-r3-y1 p)))
                                          (* (- (acl2-sine angle2))
                                             (point-in-r3-z1 p))
                                          1/4))
                            (z-of-ang2 (+ (* (acl2-sine angle2)
                                             (+ -1/4 (point-in-r3-y1 p)))
                                          (* (acl2-cosine angle2)
                                             (point-in-r3-z1 p))))
                            )
                 (:instance rot-angle1-of-angle2*p=>1
                            (x (point-in-r3-x1 p))
                            (y (point-in-r3-y1 p))
                            (z (point-in-r3-z1 p))
                            (angle1 angle1)
                            (angle2 angle2)
                            (y-of-ang2 (+ (* (acl2-cosine angle2)
                                             (+ -1/4 (point-in-r3-y1 p)))
                                          (* (- (acl2-sine angle2))
                                             (point-in-r3-z1 p))
                                          1/4))
                            (z-of-ang2 (+ (* (acl2-sine angle2)
                                             (+ -1/4 (point-in-r3-y1 p)))
                                          (* (acl2-cosine angle2)
                                             (point-in-r3-z1 p))))
                            )
                 )
           :in-theory nil
           )))

(defun zero-p (p)
  (and (point-in-r3 p)
       (= (cal-radius p) 0)))

(defthmd zero-p-lemma1
  (implies (zero-p p1)
           (and (equal (aref2 :fake-name p1 0 0) 0)
                (equal (aref2 :fake-name p1 1 0) 0)
                (equal (aref2 :fake-name p1 2 0) 0))))

(defthmd zero-p-lemma2
  (implies (and (zero-p p1)
                (zero-p p2))
           (m-= p1 p2))
  :hints (("goal"
           :use ((:instance zero-p-lemma1 (p1 p1))
                 (:instance zero-p-lemma1 (p1 p2)))
           :in-theory (e/d (m-=) (cal-radius))
           )))

(defthmd zero-p-lemma3
  (implies (and (zero-p p1)
                (point-in-r3 p2)
                (m-= p1 p2))
           (zero-p p2))
  :hints (("goal"
           :use ((:instance zero-p-lemma1 (p1 p1)))
           :in-theory (e/d (m-=) ())
           )))

(defthmd rotation-about-arbitrary-line=>r3p-m-n
  (implies (and (point-in-r3 p)
                (realp angle))
           (point-in-r3 (rotation-about-arbitrary-line angle (m-p) (n-p) p)))
  :hints (("goal"
           :use ((:instance rotation-about-arbitrary-line=>r3p (m (m-p)) (n (n-p)) (p p) (angle angle))
                 )
           :in-theory (disable rotation-about-arbitrary-line)
           )))

(defthmd rotation-about-arbitrary-line=p-m-n
  (implies (and (point-in-r3 p)
                (equal angle 0))
           (m-= (rotation-about-arbitrary-line angle (m-p) (n-p) p) p))
  :hints (("goal"
           :use ((:instance rotation-about-arbitrary-line=p (p p) (angle angle)))
           :in-theory (disable rotation-about-arbitrary-line)
           )))

(defthmd rot-angle1-of-angle2*p=>m-n
  (implies (and (point-in-r3 p)
                (realp angle1)
                (realp angle2))
           (m-= (rotation-about-arbitrary-line angle1 (m-p) (n-p)
                                               (rotation-about-arbitrary-line angle2 (m-p) (n-p) p))
                (rotation-about-arbitrary-line (+ angle1 angle2) (m-p) (n-p) p)))
  :hints (("goal"
           :use ((:instance rot-angle1-of-angle2*p=> (p p) (angle1 angle1) (angle2 angle2)))
           :in-theory (disable rotation-about-arbitrary-line)
           )))

(defthmd rot-i*angle*p-not-=p-m-n-1
  (not (zero-p (m-p)))
  :hints (("goal"
           :use ((:instance sqrt->-0 (x 29/400)))
           )))

(defthmd rot-i*angle*p-not-=p-m-n-2
  (not (zero-p (n-p)))
  :hints (("goal"
           :use ((:instance sqrt->-0 (x 349/400)))
           )))

(defun integer-seq (n)
  (if (posp n)
      (if (evenp (- n 1))
          (/ (- n 1) 2)
        (- (/ (- n 2) 2)))
    0))

(defun-sk int-exists-in-seq (int-num)
  (exists n
          (and (posp n)
               (equal (integer-seq n) int-num))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defthmd integer-seq-countable
    (implies (integerp num)
             (int-exists-in-seq num))
    :hints (("goal"
             :cases ((natp num))
             :in-theory (enable natp posp)
             )
            ("subgoal 2"
             :use ((:instance int-exists-in-seq-suff (int-num num) (n (+ (* 2 (- num)) 2))))
             )
            ("subgoal 1"
             :use ((:instance int-exists-in-seq-suff (int-num num) (n (+ (* 2 num) 1))))
             )
            ))
  )

(defun int-seq-*-pos-seq-i (i)
  (let ((rm-2 (mod-remainder-2 0 i)))
    (let ((rm-3 (mod-remainder-3 0 (nth 1 rm-2))))
      (if (equal (nth 1 rm-3) 1)
          (list (list (integer-seq (nth 0 rm-2)) (posp-seq (nth 0 rm-3))))
        (list (list (integer-seq (nth 0 rm-2)) (posp-seq (nth 0 rm-3))))))))

(encapsulate
  ()

  (local (include-book "arithmetic/top" :dir :system))

  (defun int*pos-seq-2 (i)
    (if (zp i)
        nil
      (append (int*pos-seq-2 (- i 1)) (int-seq-*-pos-seq-i i))))
  )

(defun int*pos-seq (i)
  (if (posp i)
      (int*pos-seq-2 i)
    nil))

(defun int*pos-sequence (n)
  (if (posp n)
      (nth (- n 1) (int*pos-seq n))
    (list (integer-seq 0) (posp-seq 0))))

(defthmd angle-int*pos-thm-3
  (implies (and (equal full-list (append p q))
                (true-listp p)
                (true-listp q)
                (equal (len p) len-p))
           (equal (nth len-p full-list)
                  (car q))))

(defthmd len-of-int*pos-seq-2
  (implies (posp n)
           (equal (len (int*pos-seq-2 n)) n)))

(defthmd nth-n-1-int*pos-seq=
  (implies (posp n)
           (equal (nth (- n 1) (int*pos-seq n))
                  (car (int-seq-*-pos-seq-i n))))
  :hints (("goal"
           :use ((:instance angle-int*pos-thm-3
                            (full-list (int*pos-seq-2 n))
                            (p (int*pos-seq-2 (- n 1)))
                            (q (int-seq-*-pos-seq-i n))
                            (len-p (- n 1)))
                 (:instance len-of-int*pos-seq-2 (n (- n 1)))
                 )
           :do-not-induct t
           :in-theory (disable int-seq-*-pos-seq-i)
           )))

(defthmd real-car-int-seq-*-pos-seq-i
  (implies (posp n)
           (and (realp (car (car (int-seq-*-pos-seq-i n))))
                (realp (cadr (car (int-seq-*-pos-seq-i n)))))))

(defthmd realp-int*pos-sequence
  (and (realp (car (int*pos-sequence n)))
       (realp (cadr (int*pos-sequence n))))
  :hints (("goal"
           :use ((:instance nth-n-1-int*pos-seq= (n n))
                 (:instance real-car-int-seq-*-pos-seq-i (n n))
                 )
           :in-theory (disable int*pos-seq)
           )))

(defun-sk int*pos-countable (x)
  (exists n
          (and (posp n)
               (equal (int*pos-sequence n) x))))

(defthmd int*pos-seq-exists
  (implies (and (posp n1)
                (posp n2)
                (equal (integer-seq n1) p)
                (equal (posp-seq n2) q))
           (int*pos-countable (list p q)))
  :hints (("goal"
           :use (:functional-instance f-*-g-seq-exists
                                      (f integer-seq)
                                      (g posp-seq)
                                      (f-*-g-countable int*pos-countable)
                                      (f-*-g-sequence int*pos-sequence)
                                      (f-*-g-seq int*pos-seq)
                                      (f-*-g-seq-2 int*pos-seq-2)
                                      (f-*-g-seq-i int-seq-*-pos-seq-i)
                                      (f-*-g-countable-witness int*pos-countable-witness))
           )))

(defun angle-int*pos (num pos)
  (if (posp pos)
      (/ (* 2 (acl2-pi) num) pos)
    0))

(defun generate-angle-int*pos (n)
  (if (zp n)
      nil
    (let ((num (car (int*pos-sequence n)))
          (pos (cadr (int*pos-sequence n))))
      (append (generate-angle-int*pos (- n 1)) (list (angle-int*pos num pos))))))

(defun angles-int*pos-seq (n)
  (if (posp n)
      (nth (- n 1) (generate-angle-int*pos n))
    0))

(defun-sk angle-int*pos-exists-in-seq (angle)
  (exists n
          (and (posp n)
               (equal (angles-int*pos-seq n) angle))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd angle-int*pos-thm-2
    (implies (posp n)
             (equal (len (generate-angle-int*pos n)) n))
    :hints (("goal"
             :in-theory (disable int*pos-sequence acl2-pi angle-int*pos)
             )))
  )

(defthmd angle-int*pos-thm-1
  (implies (posp n)
           (equal (nth (- n 1) (generate-angle-int*pos n))
                  (angle-int*pos (car (int*pos-sequence n)) (cadr (int*pos-sequence n)))))
  :hints (("goal"
           :use ((:instance angle-int*pos-thm-3
                            (full-list (generate-angle-int*pos n))
                            (p (generate-angle-int*pos (- n 1)))
                            (q (list (angle-int*pos num pos)))
                            (len-p (- n 1)))
                 (:instance angle-int*pos-thm-2 (n (- n 1)))
                 )
           :do-not-induct t
           :in-theory (disable int*pos-sequence angle-int*pos)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd angle-int*pos-thm
    (implies (and (posp n1)
                  (posp n2)
                  (equal (integer-seq n1) num)
                  (equal (posp-seq n2) pos))
             (angle-int*pos-exists-in-seq (/ (* 2 (acl2-pi) num) pos)))
    :hints (("goal"
             :use ((:instance int*pos-seq-exists (n1 n1) (n2 n2) (p num) (q pos))
                   (:instance angle-int*pos-exists-in-seq-suff
                              (angle (/ (* 2 (acl2-pi) num) pos))
                              (n (int*pos-countable-witness (list num pos))))
                   (:instance angle-int*pos-thm-1
                              (n (int*pos-countable-witness (list num pos))))
                   )
             :do-not-induct t
             :in-theory (disable int*pos-sequence generate-angle-int*pos)

             )))
  )

(defthmd rot-i*angle*p=p=>angle-in-seq-1
  (implies (and (zero-p p)
                (posp i)
                (realp angle)
                (m-= (rotation-about-arbitrary-line (* i angle) (m-p) (n-p) p) p))
           (equal (acl2-cosine (* i angle)) 1))
  :hints (("goal"
           :use ((:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p p)
                            (angle (* i angle)))
                 (:instance vectr-tr-m-*rot-3d-vect-tr-values
                            (angle (* i angle))
                            (p p))
                 (:instance zero-p-lemma1 (p1 p))
                 )
           :in-theory (e/d (m-=) (rotation-about-arbitrary-line acl2-sqrt acl2-pi m-p n-p))
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd rot-i*angle*p=p=>angle-in-seq-2
    (implies (and (posp i)
                  (realp angle)
                  (equal (acl2-cosine (* i angle)) 1))
             (and (equal (* i angle) (* 2 (acl2-pi) (/ (- (* i angle) (mod (* i angle) (* 2 (acl2-pi))))
                                                       (* 2 (acl2-pi)))))
                  (integerp (/ (- (* i angle) (mod (* i angle) (* 2 (acl2-pi))))
                               (* 2 (acl2-pi))))))
    :hints (("goal"
             :use ((:instance realnum-equiv
                              (r (* i angle))
                              (x (* 2 (acl2-pi))))
                   (:instance integerp-r-mod-r-x/x
                              (r (* i angle))
                              (x (* 2 (acl2-pi))))
                   (:instance range-mod-r-x
                              (r (* i angle))
                              (x (* 2 (acl2-pi))))
                   (:instance cos2pik+x
                              (k (/ (- (* i angle) (mod (* i angle) (* 2 (acl2-pi))))
                                    (* 2 (acl2-pi))))
                              (x (mod (* i angle) (* 2 (acl2-pi)))))
                   (:instance cosine-is-1-in-0<2pi=>x=0-6
                              (x (mod (* i angle) (* 2 (acl2-pi)))))
                   )
             :in-theory (disable mod sine-of-sums cosine-of-sums)
             )))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd rot-i*angle*p=p=>angle-in-seq-3
    (implies (and (zero-p p)
                  (posp i)
                  (realp angle)
                  (m-= (rotation-about-arbitrary-line (* i angle) (m-p) (n-p) p) p))
             (angle-int*pos-exists-in-seq angle))
    :hints (("goal"
             :use ((:instance rot-i*angle*p=p=>angle-in-seq-2
                              (i i)
                              (angle angle))
                   (:instance rot-i*angle*p=p=>angle-in-seq-1 (p p) (i i) (angle angle))
                   (:instance integer-seq-countable
                              (num (/ (- (* i angle) (mod (* i angle) (* 2 (acl2-pi))))
                                      (* 2 (acl2-pi)))))
                   (:instance posp-countable-thm (num i))
                   (:instance angle-int*pos-thm
                              (n1 (int-exists-in-seq-witness (/ (- (* i angle) (mod (* i angle) (* 2 (acl2-pi))))
                                                                (* 2 (acl2-pi)))))
                              (n2 (num>=1-exists-witness i))
                              (num (/ (- (* i angle) (mod (* i angle) (* 2 (acl2-pi))))
                                      (* 2 (acl2-pi))))
                              (pos i))
                   )
             :in-theory (disable m-= rotation-about-arbitrary-line zero-p angle-int*pos-exists-in-seq
                                 integer-seq posp-seq m-p n-p (:executable-counterpart m-p)
                                 (:executable-counterpart n-p) )
             )))
  )

(defthmd realp-angle-int*pos
  (realp (angles-int*pos-seq n))
  :hints (("goal"
           :use ((:instance angle-int*pos-thm-1 (n n))
                 (:instance realp-int*pos-sequence (n n))
                 )
           :in-theory (disable generate-angle-int*pos int*pos-sequence)
           )))

(defun-sk exists-in-interval-but-not-in-angle-int*pos-seq (a b)
  (exists angle
          (and (realp angle)
               (< a angle)
               (< angle b)
               (not (angle-int*pos-exists-in-seq angle)))))

(encapsulate
  ()

  (local (include-book "nonstd/transcendentals/reals-are-uncountable-1" :dir :system))

  (defthmd existence-of-angle-not-in-int*pos-sequence
    (exists-in-interval-but-not-in-angle-int*pos-seq 0 (* 2 (acl2-pi)))
    :hints (("goal"
             :use ((:functional-instance reals-are-not-countable
                                         (seq angles-int*pos-seq)
                                         (a (lambda () 0))
                                         (b (lambda () (* 2 (acl2-pi))))
                                         (exists-in-sequence angle-int*pos-exists-in-seq)
                                         (exists-in-sequence-witness angle-int*pos-exists-in-seq-witness)
                                         (exists-in-interval-but-not-in-sequence exists-in-interval-but-not-in-angle-int*pos-seq)
                                         (exists-in-interval-but-not-in-sequence-witness exists-in-interval-but-not-in-angle-int*pos-seq-witness)))
             )
            ("subgoal 4"
             :use (
                   (:instance exists-in-interval-but-not-in-angle-int*pos-seq-suff (angle x))
                   )
             )
            ("subgoal 3"
             :in-theory (disable angle-int*pos-exists-in-seq)
             )
            ("subgoal 2"
             :use (:instance angle-int*pos-exists-in-seq-suff (n i) (angle x))
             :in-theory (disable angles-int*pos-seq)
             )
            ))
  )

(defthmd witness-not-in-angle-int*pos-sequence
  (and (realp (exists-in-interval-but-not-in-angle-int*pos-seq-witness 0 (* 2 (acl2-pi))))
       (<= 0 (exists-in-interval-but-not-in-angle-int*pos-seq-witness 0 (* 2 (acl2-pi))))
       (< (exists-in-interval-but-not-in-angle-int*pos-seq-witness 0 (* 2 (acl2-pi))) (* 2 (acl2-pi)))
       (not (angle-int*pos-exists-in-seq (exists-in-interval-but-not-in-angle-int*pos-seq-witness 0 (* 2 (acl2-pi))))))
  :hints (("goal"
           :use ((:instance existence-of-angle-not-in-int*pos-sequence))
           )))

(defun angle-const ()
  (exists-in-interval-but-not-in-angle-int*pos-seq-witness 0 (* 2 (acl2-pi))))

(defthmd angle-const-is-real
  (realp (angle-const))
  :hints (("goal"
           :use ((:instance witness-not-in-angle-int*pos-sequence)
                 )
           :in-theory (disable m-= zero-p rotation-about-arbitrary-line acl2-sqrt acl2-pi
                               exists-in-interval-but-not-in-angle-int*pos-seq)
           )))

(defthmd rot-i*angle*p-not-=p-m-n
  (implies (and (zero-p p)
                (posp i)
                (equal angle (angle-const)))
           (not (m-= (rotation-about-arbitrary-line (* i angle) (m-p) (n-p) p)
                     p)))
  :hints (("goal"
           :use ((:instance rot-i*angle*p=p=>angle-in-seq-3
                            (i i)
                            (angle (angle-const))
                            (p p))
                 (:instance witness-not-in-angle-int*pos-sequence)
                 )
           :in-theory (disable m-= zero-p rotation-about-arbitrary-line acl2-sqrt acl2-pi
                               exists-in-interval-but-not-in-angle-int*pos-seq)
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd rot-i*angle*p-in-b^3
    (implies (and (zero-p p)
                  (realp angle))
             (<= (cal-radius (rotation-about-arbitrary-line angle (m-p) (n-p) p)) 1))
    :hints (("goal"
             :use ((:instance vectr-tr-m-*rot-3d-vect-tr-values (p p) (angle angle))
                   (:instance sin**2+cos**2 (x angle))
                   (:instance cosine-<-1-if-sine-non-0 (x angle))
                   (:instance r-theta*p=p=>cosine=1-1 (angle angle))
                   (:instance zero-p-lemma1 (p1 p))
                   )
             :in-theory (e/d (zero-p) (rotation-about-arbitrary-line sin**2+cos**2 cosine-<-1-if-sine-non-0))
             ))))

(defun-sk exists-z-p (i point)
  (exists p
          (and (zero-p p)
               (m-= (rotation-about-arbitrary-line (* i (angle-const)) (m-p) (n-p) p) point))))

(defthmd exists-z-p=>
  (implies (exists-z-p i point)
           (and (zero-p (exists-z-p-witness i point))
                (m-= (rotation-about-arbitrary-line (* i (angle-const)) (m-p) (n-p) (exists-z-p-witness i point))
                     point)))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-3d rotation-about-arbitrary-line)
           )))

(defun-sk ffunc (point)
  (exists i
          (and (natp i)
               (exists-z-p i point))))

(defun set-f-p (point)
  (and (point-in-r3 point)
       (ffunc point)))

(defun-sk rot-sqrt-2*f-func-1 (point)
  (exists p
          (and (set-f-p p)
               (m-= (rotation-about-arbitrary-line (angle-const) (m-p) (n-p) p) point))))

(defthmd rot-sqrt-2*f-func-1=>
  (implies (rot-sqrt-2*f-func-1 point)
           (and (set-f-p (rot-sqrt-2*f-func-1-witness point))
                (m-= (rotation-about-arbitrary-line (angle-const) (m-p) (n-p) (rot-sqrt-2*f-func-1-witness point))
                     point)))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-3d ffunc rotation-about-arbitrary-line)
           )))

(defun rot-sqrt-2*f-func (point)
  (and (point-in-r3 point)
       (rot-sqrt-2*f-func-1 point)))

(defun ffunc-not-z (point)
  (and (set-f-p point)
       (not (zero-p point))))

(defthmd rot-sqrt-2*f-func=>f-1
  (implies (and (realp x)
                (natp i))
           (realp (* i x))))

(defthmd rot-sqrt-2*f-func=>f-2
  (implies (natp i)
           (and (natp (+ i 1))
                (posp (+ i 1)))))

(defthmd rot-sqrt-2*f-func=>f-3
  (equal (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
               1)
            (angle-const))
         (+ (angle-const)
            (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
               (angle-const)))))

(defthmd rot-sqrt-2*ffunc=>f-not-z
  (implies (rot-sqrt-2*f-func point)
           (and (set-f-p point)
                (m-=
                 (rotation-about-arbitrary-line
                  (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                        1)
                     (angle-const))
                  (m-p)
                  (n-p)
                  (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                      (rot-sqrt-2*f-func-1-witness point)))
                 point)
                (zero-p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                            (rot-sqrt-2*f-func-1-witness point)))
                (realp (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                             1)
                          (angle-const)))
                (not (zero-p point))))
  :hints (("goal"
           :use ((:instance rot-sqrt-2*f-func (point point))
                 (:instance rot-sqrt-2*f-func-1=> (point point))
                 (:instance set-f-p (point (rot-sqrt-2*f-func-1-witness point)))
                 (:instance ffunc (point (rot-sqrt-2*f-func-1-witness point)))
                 (:instance exists-z-p=> (i (ffunc-witness (rot-sqrt-2*f-func-1-witness point)))
                            (point (rot-sqrt-2*f-func-1-witness point)))
                 (:instance set-f-p (point point))
                 (:instance ffunc-suff (i (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point)) 1)) (point point))
                 (:instance exists-z-p-suff (p (exists-z-p-witness
                                                (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                (rot-sqrt-2*f-func-1-witness point)))
                            (i (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point)) 1))
                            (point point))
                 (:instance rotation-about-arbitrary-line=>1
                            (p1 (rot-sqrt-2*f-func-1-witness point))
                            (m (m-p))
                            (n (n-p))
                            (angle (angle-const))
                            (p2 (rotation-about-arbitrary-line
                                 (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                    (angle-const))
                                 (m-p)
                                 (n-p)
                                 (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                     (rot-sqrt-2*f-func-1-witness point)))))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                   (rot-sqrt-2*f-func-1-witness point)))
                            (angle (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                      (angle-const))))
                 (:instance zero-p (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                          (rot-sqrt-2*f-func-1-witness point))))
                 (:instance rot-sqrt-2*f-func=>f-1
                            (x (angle-const))
                            (i (ffunc-witness (rot-sqrt-2*f-func-1-witness point))))
                 (:instance angle-const-is-real)
                 (:instance rot-sqrt-2*f-func=>f-2
                            (i (ffunc-witness (rot-sqrt-2*f-func-1-witness point))))
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (angle1 (angle-const))
                            (angle2 (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                       (angle-const)))
                            (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                   (rot-sqrt-2*f-func-1-witness point))))
                 (:instance m-=-is-an-equivalence
                            (x point)
                            (y (rotation-about-arbitrary-line (angle-const)
                                                              (m-p)
                                                              (n-p)
                                                              (rot-sqrt-2*f-func-1-witness point)))
                            (z (rotation-about-arbitrary-line
                                (+ (angle-const)
                                   (* (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                      (angle-const)))
                                (m-p)
                                (n-p)
                                (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                    (rot-sqrt-2*f-func-1-witness point)))))
                 (:instance rot-sqrt-2*f-func=>f-3)
                 (:instance rot-i*angle*p-not-=p-m-n
                            (i (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                  1))
                            (angle (angle-const))
                            (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                   (rot-sqrt-2*f-func-1-witness point))))
                 (:instance zero-p-lemma2
                            (p2 (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                    (rot-sqrt-2*f-func-1-witness point)))
                            (p1 (rotation-about-arbitrary-line
                                 (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                       1)
                                    (angle-const))
                                 (m-p)
                                 (n-p)
                                 (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                     (rot-sqrt-2*f-func-1-witness point)))))
                 (:instance zero-p-lemma3
                            (p1 point)
                            (p2 (rotation-about-arbitrary-line
                                 (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                       1)
                                    (angle-const))
                                 (m-p)
                                 (n-p)
                                 (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                     (rot-sqrt-2*f-func-1-witness point)))))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (exists-z-p-witness (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                                   (rot-sqrt-2*f-func-1-witness point)))
                            (angle (* (+ (ffunc-witness (rot-sqrt-2*f-func-1-witness point))
                                         1)
                                      (angle-const))))
                 )
           :in-theory nil
           )))

(defthm f-not-z=>rot-sqrt-2*ffunc-1-1
  (implies (and (natp i)
                (not (posp i)))
           (equal i 0))
  :rule-classes nil)

(defthmd f-not-z=>rot-sqrt-2*ffunc-1-2
  (implies (posp i)
           (natp (- i 1))))


(defthmd f-not-z=>rot-sqrt-2*ffunc-1
  (implies (ffunc-not-z point)
           (and (posp (ffunc-witness point))
                (natp (- (ffunc-witness point) 1))))
  :hints (("goal"
           :cases ((posp (ffunc-witness point)))
           :use ((:instance ffunc-not-z (point point))
                 (:instance f-not-z=>rot-sqrt-2*ffunc-1-1 (i (ffunc-witness point)))
                 (:instance set-f-p (point point))
                 (:instance ffunc (point point))
                 (:instance exists-z-p (i (ffunc-witness point))
                            (point point))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (angle (* (ffunc-witness point) (angle-const)))
                            (p (exists-z-p-witness (ffunc-witness point)
                                                   point)))
                 (:instance zero-p-lemma3
                            (p1 (exists-z-p-witness (ffunc-witness point)
                                                    point))
                            (p2 point))
                 (:instance zero-p (p (exists-z-p-witness (ffunc-witness point)
                                                          point)))
                 (:instance f-not-z=>rot-sqrt-2*ffunc-1-2
                            (i (ffunc-witness point)))
                 )
           :in-theory nil
           )))

(defthmd f-not-z=>rot-sqrt-2*ffunc-2
  (equal (+ (angle-const)
            (* (+ -1 (ffunc-witness point))
               (angle-const)))
         (* (ffunc-witness point) (angle-const))))


(defthmd f-not-z=>rot-sqrt-2*ffunc
  (implies (ffunc-not-z point)
           (rot-sqrt-2*f-func point))
  :hints (("goal"
           :use ((:instance ffunc-not-z (point point))
                 (:instance set-f-p (point point))
                 (:instance ffunc (point point))
                 (:instance exists-z-p (i (ffunc-witness point)) (point point))
                 (:instance rot-sqrt-2*f-func (point point))
                 (:instance rot-sqrt-2*f-func-1-suff
                            (p (rotation-about-arbitrary-line (* (- (ffunc-witness point) 1) (angle-const))
                                                              (m-p)
                                                              (n-p)
                                                              (exists-z-p-witness (ffunc-witness point)
                                                                                  point)))
                            (point point))
                 (:instance set-f-p (point  (rotation-about-arbitrary-line (* (+ -1 (ffunc-witness point))
                                                                              (angle-const))
                                                                           (m-p)
                                                                           (n-p)
                                                                           (exists-z-p-witness (ffunc-witness point)
                                                                                               point))))
                 (:instance f-not-z=>rot-sqrt-2*ffunc-1 (point point))
                 (:instance rot-sqrt-2*f-func=>f-1
                            (x (angle-const))
                            (i (+ -1 (ffunc-witness point))))
                 (:instance angle-const-is-real)
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (exists-z-p-witness (ffunc-witness point)
                                                   point))
                            (angle (* (+ -1 (ffunc-witness point))
                                      (angle-const))))
                 (:instance zero-p (p (exists-z-p-witness (ffunc-witness point)
                                                          point)))
                 (:instance ffunc-suff (point (rotation-about-arbitrary-line (* (+ -1 (ffunc-witness point))
                                                                                (angle-const))
                                                                             (m-p)
                                                                             (n-p)
                                                                             (exists-z-p-witness (ffunc-witness point)
                                                                                                 point)))
                            (i (+ -1 (ffunc-witness point))))
                 (:instance exists-z-p-suff
                            (p (exists-z-p-witness (ffunc-witness point)
                                                   point))
                            (point (rotation-about-arbitrary-line (* (+ -1 (ffunc-witness point))
                                                                     (angle-const))
                                                                  (m-p)
                                                                  (n-p)
                                                                  (exists-z-p-witness (ffunc-witness point)
                                                                                      point)))
                            (i (+ -1 (ffunc-witness point))))
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (angle1 (angle-const))
                            (angle2 (* (+ -1 (ffunc-witness point))
                                       (angle-const)))
                            (p (exists-z-p-witness (ffunc-witness point)
                                                   point)))
                 (:instance f-not-z=>rot-sqrt-2*ffunc-2)
                 )
           :in-theory nil
           )))

(defthmd rot-sqrt-2*ffunc-iff-f-not-z
  (iff (rot-sqrt-2*f-func p)
       (ffunc-not-z p))
  :hints (("goal"
           :use ((:instance rot-sqrt-2*ffunc=>f-not-z (point p))
                 (:instance f-not-z=>rot-sqrt-2*ffunc (point p))
                 (:instance ffunc-not-z (point p))
                 )
           :in-theory nil
           )))

(defthmd cal-radius>=0
  (implies (point-in-r3 p)
           (>= (cal-radius p) 0))
  :hints (("goal"
           :in-theory (disable (:type-prescription cal-radius) (:executable-counterpart tau-system))
           )))

(defun b3 (p)
  (and (point-in-r3 p)
       (<= (cal-radius p) 1)))

(defthmd b3=>b3-0-or-0
  (iff (b3 p)
       (or (zero-p p)
           (b3-0 p)))
  :hints (("goal"
           :use ((:instance cal-radius>=0 (p p)))
           :in-theory (disable cal-radius)
           )))

(defun b3-f (p)
  (and (b3 p)
       (not (set-f-p p))))

(defthmd cal-radius-p1=p2
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= p1 p2))
           (equal (cal-radius p1)
                  (cal-radius p2)))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd f=>b3
  (implies (set-f-p p)
           (b3 p))
  :hints (("goal"
           :use ((:instance set-f-p (point p))
                 (:instance b3 (p p))
                 (:instance ffunc (point p))
                 (:instance exists-z-p=> (i (ffunc-witness p)) (point p))
                 (:instance cal-radius-p1=p2 (p1 (rotation-about-arbitrary-line (* (ffunc-witness p) (angle-const))
                                                                                (m-p)
                                                                                (n-p)
                                                                                (exists-z-p-witness (ffunc-witness p)
                                                                                                    p)))
                            (p2 p))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (exists-z-p-witness (ffunc-witness p)
                                                   p))
                            (angle (* (ffunc-witness p) (angle-const))))
                 (:instance zero-p (p (exists-z-p-witness (ffunc-witness p)
                                                          p)))
                 (:instance rot-sqrt-2*f-func=>f-1
                            (x (angle-const))
                            (i (ffunc-witness p)))
                 (:instance angle-const-is-real)
                 (:instance rot-i*angle*p-in-b^3 (p (exists-z-p-witness (ffunc-witness p)
                                                                        p))
                            (angle (* (ffunc-witness p) (angle-const))))
                 )
           :in-theory nil
           )))

(defthmd b3=>
  (iff (b3 p)
       (or (b3-f p)
           (set-f-p p)))
  :hints (("goal"
           :use ((:instance f=>b3))
           :in-theory (disable set-f-p b3)
           )))

(defthmd z=>f-1
  (natp 0))

(defthmd z=>f
  (implies (zero-p p)
           (set-f-p p))
  :hints (("goal"
           :use ((:instance zero-p (p p))
                 (:instance set-f-p (point p))
                 (:instance ffunc-suff (i 0) (point p))
                 (:instance z=>f-1)
                 (:instance exists-z-p-suff (p p) (i 0) (point p))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (angle (* 0 (angle-const)))
                            (p p))
                 )
           :in-theory nil
           )))

(defun b3-0-n-b3-f (p)
  (and (b3-0 p)
       (b3-f p)))

(defthm b3-0-n-b3-f-iff-b3-f
  (iff (b3-f p)
       (b3-0-n-b3-f p))
  :hints (("goal"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b3-f (p p))
                 (:instance b3=>b3-0-or-0 (p p))
                 (:instance z=>f (p p))
                 )
           :in-theory nil
           )))

(defun b3-0-n-f (p)
  (and (b3-0 p)
       (set-f-p p)))

(defthmd b3-0=>not-z
  (implies (b3-0 p)
           (not (zero-p p)))
  :hints (("goal"
           :use ((:instance b3-0 (p p))
                 (:instance zero-p (p p))
                 )
           :in-theory nil
           )))

(defthmd f-not-z-iff-b3-0-n-f
  (iff (ffunc-not-z p)
       (b3-0-n-f p))
  :hints (("goal"
           :use ((:instance ffunc-not-z (point p))
                 (:instance b3-0-n-f (p p))
                 (:instance z=>f (p p))
                 (:instance b3=>)
                 (:instance b3=>b3-0-or-0)
                 (:instance b3-0=>not-z (p p))
                 )
           :in-theory nil
           )))

(defun-sk rota-1-rota-f-1 (point)
  (exists p
          (and (rot-sqrt-2*f-func p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p)
                    point))))

(defun rota-1-rota-f (p)
  (and (point-in-r3 p)
       (rota-1-rota-f-1 p)))

(defthmd rota-1-rota-f-iff-set-f-p-1
  (implies (set-f-p p)
           (rota-1-rota-f p))
  :hints (("goal"
           :use ((:instance rota-1-rota-f (p p))
                 (:instance set-f-p (point p))
                 (:instance rota-1-rota-f-1-suff
                            (p (rotation-about-arbitrary-line (angle-const) (m-p) (n-p) p))
                            (point p))
                 (:instance rot-sqrt-2*f-func (point (rotation-about-arbitrary-line (angle-const)
                                                                                    (m-p)
                                                                                    (n-p)
                                                                                    p)))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (angle (angle-const))
                            (p p))
                 (:instance angle-const-is-real)
                 (:instance rot-sqrt-2*f-func-1-suff
                            (p p)
                            (point (rotation-about-arbitrary-line (angle-const)
                                                                  (m-p)
                                                                  (n-p)
                                                                  p)))
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (p p)
                            (angle1 (- (angle-const)))
                            (angle2 (angle-const)))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (angle (+ (- (angle-const)) (angle-const)))
                            (p p))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rota-f-iff-set-f-p-2-1
  (implies (and (m-= p1 p2)
                (point-in-r3 p2)
                (set-f-p p1))
           (set-f-p p2))
  :hints (("goal"
           :use ((:instance set-f-p (point p1))
                 (:instance ffunc (point p1))
                 (:instance exists-z-p (point p1)
                            (i (ffunc-witness p1)))
                 (:instance set-f-p (point p2))
                 (:instance ffunc-suff
                            (i (ffunc-witness p1))
                            (point p2))
                 (:instance exists-z-p-suff (i (ffunc-witness p1))
                            (p (exists-z-p-witness (ffunc-witness p1)
                                                   p1))
                            (point p2))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rota-f-iff-set-f-p-2
  (implies (rota-1-rota-f p)
           (set-f-p p))
  :hints (("goal"
           :use ((:instance rota-1-rota-f (p p))
                 (:instance rota-1-rota-f-1 (point p))
                 (:instance rot-sqrt-2*f-func (point (rota-1-rota-f-1-witness p)))
                 (:instance rot-sqrt-2*f-func-1 (point (rota-1-rota-f-1-witness p)))
                 (:instance rotation-about-arbitrary-line=>1
                            (p1 (rota-1-rota-f-1-witness p))
                            (p2 (rotation-about-arbitrary-line
                                 (angle-const)
                                 (m-p)
                                 (n-p)
                                 (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p))))
                            (angle (- (angle-const)))
                            (m (m-p))
                            (n (n-p)))
                 (:instance set-f-p (point (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p))))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p)))
                            (angle (angle-const)))
                 (:instance angle-const-is-real)
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (angle1 (- (angle-const)))
                            (angle2 (angle-const))
                            (p (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p))))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (angle (+ (- (angle-const)) (angle-const)))
                            (p (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p))))
                 (:instance set-f-p (point p))
                 (:instance rota-1-rota-f-iff-set-f-p-2-1
                            (p1 (rot-sqrt-2*f-func-1-witness (rota-1-rota-f-1-witness p)))
                            (p2 p))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rota-f-iff-set-f-p
  (iff (set-f-p p)
       (rota-1-rota-f p))
  :hints (("goal"
           :use ((:instance rota-1-rota-f-iff-set-f-p-1)
                 (:instance rota-1-rota-f-iff-set-f-p-2))
           )))

(defun-sk rota-inv-b3-0-n-f-1 (point)
  (exists p
          (and (b3-0-n-f p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p)
                    point))))

(defun rota-inv-b3-0-n-f (p)
  (and (point-in-r3 p)
       (rota-inv-b3-0-n-f-1 p)))


(defthmd f-iff-rota-inv-b3-0-n-f-1
  (implies (set-f-p p)
           (rota-inv-b3-0-n-f p))
  :hints (("goal"
           :use ((:instance rota-inv-b3-0-n-f (p p))
                 (:instance set-f-p (point p))
                 (:instance rota-1-rota-f-iff-set-f-p (p p))
                 (:instance rota-1-rota-f (p p))
                 (:instance rota-1-rota-f-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rot-sqrt-2*ffunc-iff-f-not-z (p (rota-1-rota-f-1-witness p)))
                 (:instance f-not-z-iff-b3-0-n-f (p (rota-1-rota-f-1-witness p)))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (p (rota-1-rota-f-1-witness p))
                            (point p))
                 )
           :in-theory nil
           )))

(defthmd f-iff-rota-inv-b3-0-n-f-2
  (implies (rota-inv-b3-0-n-f p)
           (set-f-p p))
  :hints (("goal"
           :use ((:instance rota-inv-b3-0-n-f (p p))
                 (:instance set-f-p (point p))
                 (:instance rota-inv-b3-0-n-f-1 (point p))
                 (:instance f-not-z-iff-b3-0-n-f (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-sqrt-2*ffunc-iff-f-not-z
                            (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-sqrt-2*f-func
                            (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-sqrt-2*f-func-1
                            (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotation-about-arbitrary-line=>1
                            (p1 (rota-inv-b3-0-n-f-1-witness p))
                            (p2 (rotation-about-arbitrary-line
                                 (angle-const)
                                 (m-p)
                                 (n-p)
                                 (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                            (angle (- (angle-const)))
                            (m (m-p))
                            (n (n-p)))
                 (:instance set-f-p (point (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rotation-about-arbitrary-line=>r3p-m-n
                            (p (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                            (angle (angle-const)))
                 (:instance angle-const-is-real)
                 (:instance rot-angle1-of-angle2*p=>m-n
                            (p (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                            (angle1 (- (angle-const)))
                            (angle2 (angle-const)))
                 (:instance rotation-about-arbitrary-line=p-m-n
                            (p (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                            (angle (+ (- (angle-const)) (angle-const))))
                 (:instance rota-1-rota-f-iff-set-f-p-2-1
                            (p1 (rot-sqrt-2*f-func-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                            (p2 p))
                 )
           :in-theory nil
           )))

(defthmd f-iff-rota-inv-b3-0-n-f
  (iff (set-f-p p)
       (rota-inv-b3-0-n-f p))
  :hints (("goal"
           :use ((:instance f-iff-rota-inv-b3-0-n-f-1)
                 (:instance f-iff-rota-inv-b3-0-n-f-2)
                 )
           )))

(defthmd b3-iff-b3-0-n-b3-f-or-rota-inv-b3-0-n-f
  (iff (b3 p)
       (or (b3-0-n-b3-f p)
           (rota-inv-b3-0-n-f p)))
  :hints (("goal"
           :use ((:instance b3=> (p p))
                 (:instance b3-0-n-b3-f-iff-b3-f (p p))
                 (:instance f-iff-rota-inv-b3-0-n-f (p p))
                 )
           :in-theory nil
           )))

(defun-sk rot*b3-f-1 (rot point)
  (exists p
          (and (b3-f p)
               (m-= (m-* rot p) point))))

(defun rot*b3-f (rot p)
  (and (point-in-r3 p)
       (rot*b3-f-1 rot p)))

(defun-sk rot*set-f-1 (rot point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* rot p) point))))

(defun rot*set-f (rot p)
  (and (point-in-r3 p)
       (rot*set-f-1 rot p)))

(defthmd rot*b3-in-b3
  (implies (and (b3 p)
                (r3-rotationp rot))
           (b3 (m-* rot p)))
  :hints (("goal"
           :use ((:instance b3 (p p))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (p2 (m-* rot p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot rot))
                 (:instance r3-rotationp (m rot))
                 (:instance b3 (p (m-* rot p)))
                 )
           :in-theory nil
           )))

(defthmd rotp-rot=>rot*b3-f-or-rot-sf=>b3-1
  (implies (and (m-= (m-* m1 m2) m3)
                (m-= (m-* m3 m4) m5))
           (m-= (m-* m1 m2 m4) m5)))


(defthmd rotp-rot=>b3=>rot*b3-f-or-rot-sf
  (implies (and (r3-rotationp rot)
                (b3 p))
           (or (rot*b3-f rot p)
               (rot*set-f rot p)))
  :hints (("goal"
           :use ((:instance b3 (p p))
                 (:instance rot*b3-f (rot rot) (p p))
                 (:instance rot*b3-f-1-suff (p (m-* (r3-m-inverse rot) p)) (rot rot) (point p))
                 (:instance rot*set-f (rot rot) (p p))
                 (:instance rot*set-f-1-suff (p (m-* (r3-m-inverse rot) p)) (rot rot) (point p))
                 (:instance rot*b3-in-b3
                            (rot (r3-m-inverse rot))
                            (p p))
                 (:instance rot-m=>rot-m-inv (m rot))
                 (:instance b3-f (p (m-* (r3-m-inverse rot) p)))
                 (:instance m-*-m-m-inverse (m rot))
                 (:instance r3-rotationp (m rot))
                 (:instance m-*point-id=point (p1 p))
                 (:instance rotp-rot=>rot*b3-f-or-rot-sf=>b3-1
                            (m1 rot)
                            (m2 (r3-m-inverse rot))
                            (m4 p)
                            (m3 (id-rotation))
                            (m5 p))
                 )
           :in-theory nil
           )))

(defthmd rotp-rot=>rot*b3-f-or-rot-sf=>b3
  (implies (and (r3-rotationp rot)
                (or (rot*b3-f rot p)
                    (rot*set-f rot p)))
           (b3 p))
  :hints (("goal"
           :use ((:instance b3 (p p))
                 (:instance rot*b3-f (rot rot) (p p))
                 (:instance rot*b3-f-1 (rot rot) (point p))
                 (:instance rot*set-f (rot rot) (p p))
                 (:instance rot*set-f-1 (rot rot) (point p))
                 (:instance rot*b3-in-b3
                            (p (rot*b3-f-1-witness rot p))
                            (rot rot))
                 (:instance b3-f (p (rot*b3-f-1-witness rot p)))
                 (:instance b3 (p (m-* rot (rot*b3-f-1-witness rot p))))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* rot (rot*b3-f-1-witness rot p)))
                            (p2 p))
                 (:instance rot*b3-in-b3
                            (p (rot*set-f-1-witness rot p))
                            (rot rot))
                 (:instance f=>b3
                            (p (rot*set-f-1-witness rot p)))
                 (:instance b3 (p (m-* rot (rot*set-f-1-witness rot p))))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* rot (rot*set-f-1-witness rot p)))
                            (p2 p))
                 )
           :in-theory nil
           )))

(defthmd rotp-rot=>rot*b3-f-or-rot-sf-iff-b3
  (implies (r3-rotationp rot)
           (iff (or (rot*b3-f rot p)
                    (rot*set-f rot p))
                (b3 p)))
  :hints (("goal"
           :use ((:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf)
                 (:instance rotp-rot=>rot*b3-f-or-rot-sf=>b3))
           :in-theory nil
           )))

(defun rot-3 ()
  (a-inv-rotation (acl2-sqrt 2)))

(defun rot-4 ()
  (m-* (a-inv-rotation (acl2-sqrt 2))
       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

(defun rot-5 ()
  (m-* (rotation-3d
        (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
       (a-inv-rotation (acl2-sqrt 2))))

(defun rot-6 ()
  (m-* (rotation-3d
        (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
       (a-inv-rotation (acl2-sqrt 2))
       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

(defun rot-7 ()
  (id-rotation))

(defun rot-8 ()
  (id-rotation))

(defun-sk rot-3-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-3)) p) point))))

(defun b3-01 (p)
  (and (b3-0-set-a3 p)
       (b3-f p)
       (rot-3-inv*f p)))

(defun b3-11 (p)
  (and (b3-0-set-a3 p)
       (set-f-p p)
       (rot-3-inv*f p)))

(defun-sk rota-1-rot-3-b3-01-1 (point)
  (exists p
          (and (b3-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-3) p))
                    point))))

(defun rota-1-rot-3-b3-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-3-b3-01-1 p)))

(defun-sk rota-1-rot-3-b3-11-1 (point)
  (exists p
          (and (b3-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-3) p))
                    point))))

(defun rota-1-rot-3-b3-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-3-b3-11-1 p)))

(defun-sk rot-4-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-4)) p) point))))

(defun b4-01 (p)
  (and (b3-0-set-a4 p)
       (b3-f p)
       (rot-4-inv*f p)))

(defun b4-11 (p)
  (and (b3-0-set-a4 p)
       (set-f-p p)
       (rot-4-inv*f p)))

(defun-sk rota-1-rot-4-b4-01-1 (point)
  (exists p
          (and (b4-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-4) p))
                    point))))

(defun rota-1-rot-4-b4-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-4-b4-01-1 p)))

(defun-sk rota-1-rot-4-b4-11-1 (point)
  (exists p
          (and (b4-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-4) p))
                    point))))

(defun rota-1-rot-4-b4-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-4-b4-11-1 p)))

(defun-sk rot-5-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-5)) p) point))))

(defun b5-01 (p)
  (and (b3-0-set-a5 p)
       (b3-f p)
       (rot-5-inv*f p)))

(defun b5-11 (p)
  (and (b3-0-set-a5 p)
       (set-f-p p)
       (rot-5-inv*f p)))

(defun-sk rota-1-rot-5-b5-01-1 (point)
  (exists p
          (and (b5-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-5) p))
                    point))))

(defun rota-1-rot-5-b5-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-5-b5-01-1 p)))

(defun-sk rota-1-rot-5-b5-11-1 (point)
  (exists p
          (and (b5-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-5) p))
                    point))))

(defun rota-1-rot-5-b5-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-5-b5-11-1 p)))

(defun-sk rot-6-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-6)) p) point))))

(defun b6-01 (p)
  (and (b3-0-set-a6 p)
       (b3-f p)
       (rot-6-inv*f p)))

(defun b6-11 (p)
  (and (b3-0-set-a6 p)
       (set-f-p p)
       (rot-6-inv*f p)))

(defun-sk rota-1-rot-6-b6-01-1 (point)
  (exists p
          (and (b6-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-6) p))
                    point))))

(defun rota-1-rot-6-b6-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-6-b6-01-1 p)))

(defun-sk rota-1-rot-6-b6-11-1 (point)
  (exists p
          (and (b6-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-6) p))
                    point))))

(defun rota-1-rot-6-b6-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-6-b6-11-1 p)))

(defun-sk rot-7-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-7)) p) point))))

(defun b7-01 (p)
  (and (b3-0-set-a7 p)
       (b3-f p)
       (rot-7-inv*f p)))

(defun b7-11 (p)
  (and (b3-0-set-a7 p)
       (set-f-p p)
       (rot-7-inv*f p)))

(defun-sk rota-1-rot-7-b7-01-1 (point)
  (exists p
          (and (b7-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-7) p))
                    point))))

(defun rota-1-rot-7-b7-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-7-b7-01-1 p)))

(defun-sk rota-1-rot-7-b7-11-1 (point)
  (exists p
          (and (b7-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-7) p))
                    point))))

(defun rota-1-rot-7-b7-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-7-b7-11-1 p)))

(defun-sk rot-8-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-8)) p) point))))

(defun b8-01 (p)
  (and (b3-0-set-a8 p)
       (b3-f p)
       (rot-8-inv*f p)))

(defun b8-11 (p)
  (and (b3-0-set-a8 p)
       (set-f-p p)
       (rot-8-inv*f p)))

(defun-sk rota-1-rot-8-b8-01-1 (point)
  (exists p
          (and (b8-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-8) p))
                    point))))

(defun rota-1-rot-8-b8-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-8-b8-01-1 p)))

(defun-sk rota-1-rot-8-b8-11-1 (point)
  (exists p
          (and (b8-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-8) p))
                    point))))

(defun rota-1-rot-8-b8-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-8-b8-11-1 p)))

(defthmd a3-a8-rot-a-inv-b3-0-nf=>1
  (implies (and (m-= (m-* m1 m2) m3)
                (m-= (m-* m4 m1) m5)
                (m-= (m-* m5 m2) m6))
           (m-= (m-* m4 m3) m6)))

(defthm a3-a8-rot-a-inv-b3-0-nf=>sub-3
  (equal (m-* (m-* m1 m2 m3) m4)
         (m-* m1 m2 m3 m4))
  :hints (("goal"
           :use ((:instance associativity-of-m-*-3
                            (m1 m1)
                            (m2 m2)
                            (m3 m3))
                 (:instance associativity-of-m-*-2
                            (m1 m1)
                            (m2 m2)
                            (m3 m3))
                 (:instance associativity-of-m-*
                            (m1 m1)
                            (m2 (m-* m2 m3))
                            (m3 m4))
                 (:instance associativity-of-m-*-2
                            (m1 m2)
                            (m2 m3)
                            (m3 m4))
                 )
           ))
  :rule-classes nil
  )

(defthmd a3-a8-rot-a-inv-b3-0-nf=>
  (implies (rota-inv-b3-0-n-f p)
           (or (rota-1-rot-3-b3-11 p)
               (rota-1-rot-3-b3-01 p)
               (rota-1-rot-4-b4-11 p)
               (rota-1-rot-4-b4-01 p)
               (rota-1-rot-5-b5-11 p)
               (rota-1-rot-5-b5-01 p)
               (rota-1-rot-6-b6-11 p)
               (rota-1-rot-6-b6-01 p)
               (rota-1-rot-7-b7-11 p)
               (rota-1-rot-7-b7-01 p)
               (rota-1-rot-8-b8-11 p)
               (rota-1-rot-8-b8-01 p)))
  :hints (("goal"
           :cases ((b3-0-a-inv-b3-0-set-a3 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-a-inv-r-b3-0-set-a4 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-r-1-a-inv-b3-0-set-a5 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-r-1-a-inv-r-b3-0-set-a6 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a7 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a8 (rota-inv-b3-0-n-f-1-witness p)))
           :use ((:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1 (point p))
                 (:instance b3-0-n-f (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3-0-iff-a3-to-a8 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 6"
           :use((:instance b3-0-a-inv-b3-0-set-a3 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-a-inv-b3-0-set-a3-1 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-3-b3-01 (p p))
                (:instance rota-1-rot-3-b3-11 (p p))
                (:instance rota-1-rot-3-b3-01-1-suff
                           (point p)
                           (p (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-01
                           (p (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rota-1-rot-3-b3-11-1-suff
                           (point p)
                           (p (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-11
                           (p (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-f
                           (p (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0-iff-a1-to-a14
                           (p (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0
                           (p (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3 (p (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rot-3-inv*f-suff
                           (point (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-3)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-3))
                           (m2 (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-3)))
                           (m5 (id-rotation))
                           (m6 (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance m-*-m-inverse-m
                           (m (rot-3)))
                (:instance m-*point-id=point
                           (p1 (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (a-inv-rotation (acl2-sqrt 2))))
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-3)
                                    (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (b3-0-a-inv-b3-0-set-a3-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (rot (rot-3)))
                )
           :in-theory nil
           )
          ("subgoal 5"
           :use((:instance b3-0-a-inv-r-b3-0-set-a4 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-a-inv-r-b3-0-set-a4-1 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-4-b4-01 (p p))
                (:instance rota-1-rot-4-b4-11 (p p))
                (:instance rota-1-rot-4-b4-01-1-suff
                           (point p)
                           (p (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b4-01
                           (p (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rota-1-rot-4-b4-11-1-suff
                           (point p)
                           (p (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b4-11
                           (p (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-f
                           (p (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0-iff-a1-to-a14
                           (p (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0
                           (p (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3 (p (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rot-4-inv*f-suff
                           (point (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-4)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-4))
                           (m2 (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-4)))
                           (m5 (id-rotation))
                           (m6 (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance associativity-of-m-*
                           (m1 (a-inv-rotation (acl2-sqrt 2)))
                           (m2 (rotation-3d
                                (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                (point-on-s2-not-d)))
                           (m3 (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance m-*-m-inverse-m
                           (m (rot-4)))
                (:instance rot*rot-is-rot
                           (m1 (a-inv-rotation (acl2-sqrt 2)))
                           (m2 (rotation-3d
                                (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                (point-on-s2-not-d))))
                (:instance m-*point-id=point
                           (p1 (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (rot-4)))
                (:instance r3-rotationp-r-theta
                           (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                (:instance witness-not-in-angle-sequence)
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-4)
                                    (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (b3-0-a-inv-r-b3-0-set-a4-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (rot (rot-4)))
                )
           :in-theory nil
           )
          ("subgoal 4"
           :use((:instance b3-0-r-1-a-inv-b3-0-set-a5 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-r-1-a-inv-b3-0-set-a5-1 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-5-b5-01 (p p))
                (:instance rota-1-rot-5-b5-11 (p p))
                (:instance rota-1-rot-5-b5-01-1-suff
                           (point p)
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b5-01
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rota-1-rot-5-b5-11-1-suff
                           (point p)
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b5-11
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-f
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0-iff-a1-to-a14
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0
                           (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3 (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rot-5-inv*f-suff
                           (point (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-5)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-5))
                           (m2 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-5)))
                           (m5 (id-rotation))
                           (m6 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance associativity-of-m-*
                           (m2 (a-inv-rotation (acl2-sqrt 2)))
                           (m1 (rotation-3d
                                (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                (point-on-s2-not-d)))
                           (m3 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance m-*-m-inverse-m
                           (m (rot-5)))
                (:instance rot*rot-is-rot
                           (m2 (a-inv-rotation (acl2-sqrt 2)))
                           (m1 (rotation-3d
                                (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                (point-on-s2-not-d))))
                (:instance m-*point-id=point
                           (p1 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (rot-5)))
                (:instance r3-rotationp-r-theta
                           (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                (:instance witness-not-in-angle-sequence)
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-5)
                                    (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (rot (rot-5)))
                )
           :in-theory nil
           )
          ("subgoal 3"
           :use((:instance b3-0-r-1-a-inv-r-b3-0-set-a6 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-r-1-a-inv-r-b3-0-set-a6-1 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-6-b6-01 (p p))
                (:instance rota-1-rot-6-b6-11 (p p))
                (:instance rota-1-rot-6-b6-01-1-suff
                           (point p)
                           (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b6-01
                           (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rota-1-rot-6-b6-11-1-suff
                           (point p)
                           (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b6-11
                           (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-f
                           (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0-iff-a1-to-a14
                           (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0
                           (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3 (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rot-6-inv*f-suff
                           (point (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-6)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-6))
                           (m2 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-6)))
                           (m5 (id-rotation))
                           (m6 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance associativity-of-m-*
                           (m2 (a-inv-rotation (acl2-sqrt 2)))
                           (m1 (rotation-3d
                                (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                (point-on-s2-not-d)))
                           (m3 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness
                                (rota-inv-b3-0-n-f-1-witness p))))
                (:instance a3-a8-rot-a-inv-b3-0-nf=>sub-3
                           (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                0 (* 2 (acl2-pi))))
                                            (point-on-s2-not-d)))
                           (m2 (a-inv-rotation (acl2-sqrt 2)))
                           (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                           (m4 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness
                                (rota-inv-b3-0-n-f-1-witness p))))
                (:instance m-*-m-inverse-m
                           (m (rot-6)))
                (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                           (m2 (a-inv-rotation (acl2-sqrt 2)))
                           (m1 (rotation-3d
                                (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                (point-on-s2-not-d)))
                           (m3 (rotation-3d
                                (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                (point-on-s2-not-d))))
                (:instance m-*point-id=point
                           (p1 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (rot-6)))
                (:instance r3-rotationp-r-theta
                           (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                (:instance r3-rotationp-r-theta
                           (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                (:instance witness-not-in-angle-sequence)
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-6)
                                    (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (rot (rot-6)))
                )
           :in-theory nil
           )
          ("subgoal 2"
           :use((:instance b3-0-set-a7 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-7-b7-01 (p p))
                (:instance rota-1-rot-7-b7-11 (p p))
                (:instance rota-1-rot-7-b7-01-1-suff
                           (point p)
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b7-01
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-7-b7-11-1-suff
                           (point p)
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b7-11
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-f
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-iff-a1-to-a14
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-7-inv*f-suff
                           (point (rota-inv-b3-0-n-f-1-witness p))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-7)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-7))
                           (m2 (rota-inv-b3-0-n-f-1-witness p))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-7)))
                           (m5 (id-rotation))
                           (m6 (rota-inv-b3-0-n-f-1-witness p)))
                (:instance m-*-m-inverse-m
                           (m (rot-7)))
                (:instance m-*point-id=point
                           (p1 (rota-inv-b3-0-n-f-1-witness p)))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (id-rotation)))
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-7)
                                    (rota-inv-b3-0-n-f-1-witness p)))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (rota-inv-b3-0-n-f-1-witness p))
                           (rot (rot-7)))
                )
           :in-theory nil
           )
          ("subgoal 1"
           :use((:instance b3-0-set-a8 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-8-b8-01 (p p))
                (:instance rota-1-rot-8-b8-11 (p p))
                (:instance rota-1-rot-8-b8-01-1-suff
                           (point p)
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b8-01
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-8-b8-11-1-suff
                           (point p)
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b8-11
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-f
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-iff-a1-to-a14
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-8-inv*f-suff
                           (point (rota-inv-b3-0-n-f-1-witness p))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-8)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-8))
                           (m2 (rota-inv-b3-0-n-f-1-witness p))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-8)))
                           (m5 (id-rotation))
                           (m6 (rota-inv-b3-0-n-f-1-witness p)))
                (:instance m-*-m-inverse-m
                           (m (rot-8)))
                (:instance m-*point-id=point
                           (p1 (rota-inv-b3-0-n-f-1-witness p)))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (id-rotation)))
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-8)
                                    (rota-inv-b3-0-n-f-1-witness p)))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (rota-inv-b3-0-n-f-1-witness p))
                           (rot (rot-8)))
                )
           :in-theory nil
           )
          ))

(defthmd rot*b3-0-set=>b3-0
  (implies (and (or (b3-0-set-a1 p)
                    (b3-0-set-a2 p)
                    (b3-0-set-a3 p)
                    (b3-0-set-a4 p)
                    (b3-0-set-a5 p)
                    (b3-0-set-a6 p)
                    (b3-0-set-a7 p)
                    (b3-0-set-a8 p)
                    (b3-0-set-a9 p)
                    (b3-0-set-a10 p)
                    (b3-0-set-a11 p)
                    (b3-0-set-a12 p)
                    (b3-0-set-a13 p)
                    (b3-0-set-a14 p))
                (r3-rotationp rot))
           (b3-0 (m-* rot p)))
  :hints (("goal"
           :use ((:instance b3-0-iff-a1-to-a14
                            (p p))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (rot rot)
                            (p2 (m-* rot p)))
                 (:instance b3-0-set-a1 (p p))
                 (:instance b3-0-set-a2 (p p))
                 (:instance b3-0-set-a3 (p p))
                 (:instance b3-0-set-a4 (p p))
                 (:instance b3-0-set-a5 (p p))
                 (:instance b3-0-set-a6 (p p))
                 (:instance b3-0-set-a7 (p p))
                 (:instance b3-0-set-a8 (p p))
                 (:instance b3-0-set-a9 (p p))
                 (:instance b3-0-set-a10 (p p))
                 (:instance b3-0-set-a11 (p p))
                 (:instance b3-0-set-a12 (p p))
                 (:instance b3-0-set-a13 (p p))
                 (:instance b3-0-set-a14 (p p))
                 (:instance b3-0 (p (m-* rot p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1 (p1 p)
                            (rot rot))
                 (:instance r3-rotationp (m rot))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rot-3-b3-01-or-11=>2
  (implies (and (r3-rotationp rot)
                (set-f-p p1)
                (point-in-r3 p2)
                (m-= (m-* (r3-m-inverse rot) p1) p2))
           (set-f-p (m-* rot p2)))
  :hints (("goal"
           :use ((:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (r3-m-inverse rot))
                            (m2 p1)
                            (m3 p2)
                            (m4 rot)
                            (m5 (id-rotation))
                            (m6 p1))
                 (:instance m-*-m-m-inverse (m rot))
                 (:instance r3-rotationp (m rot))
                 (:instance rota-1-rota-f-iff-set-f-p-2-1
                            (p1 p1)
                            (p2 (m-* rot p2)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p2)
                            (rot rot))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance set-f-p (point p1))
                 )
           :in-theory nil
           )))

(defthmd rota-1-rot-3-8-b-3-8-01-or-11=>
  (implies (or (rota-1-rot-3-b3-11 p)
               (rota-1-rot-3-b3-01 p)
               (rota-1-rot-4-b4-11 p)
               (rota-1-rot-4-b4-01 p)
               (rota-1-rot-5-b5-11 p)
               (rota-1-rot-5-b5-01 p)
               (rota-1-rot-6-b6-11 p)
               (rota-1-rot-6-b6-01 p)
               (rota-1-rot-7-b7-11 p)
               (rota-1-rot-7-b7-01 p)
               (rota-1-rot-8-b8-11 p)
               (rota-1-rot-8-b8-01 p))
           (rota-inv-b3-0-n-f p))
  :hints (("goal"
           :cases ((or (rota-1-rot-3-b3-11 p)
                       (rota-1-rot-3-b3-01 p))
                   (or (rota-1-rot-4-b4-11 p)
                       (rota-1-rot-4-b4-01 p))
                   (or (rota-1-rot-5-b5-11 p)
                       (rota-1-rot-5-b5-01 p))
                   (or (rota-1-rot-6-b6-11 p)
                       (rota-1-rot-6-b6-01 p))
                   (or (rota-1-rot-7-b7-11 p)
                       (rota-1-rot-7-b7-01 p))
                   (or (rota-1-rot-8-b8-11 p)
                       (rota-1-rot-8-b8-01 p)))
           :in-theory nil)
          ("subgoal 6"
           :use ((:instance rota-1-rot-3-b3-11 (p p))
                 (:instance rota-1-rot-3-b3-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-3)
                                    (rota-1-rot-3-b3-11-1-witness p))))
                 (:instance b3-11 (p (rota-1-rot-3-b3-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-3))
                            (p (rota-1-rot-3-b3-11-1-witness p)))
                 (:instance b3-0-set-a3 (p (rota-1-rot-3-b3-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-3)
                                             (rota-1-rot-3-b3-11-1-witness p))))
                 (:instance rot-3-inv*f (point (rota-1-rot-3-b3-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-3))
                            (p1 (rot-3-inv*f-witness (rota-1-rot-3-b3-11-1-witness p)))
                            (p2 (rota-1-rot-3-b3-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-3)
                 (:instance rota-1-rot-3-b3-01 (p p))
                 (:instance rota-1-rot-3-b3-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-3)
                                    (rota-1-rot-3-b3-01-1-witness p))))
                 (:instance b3-01 (p (rota-1-rot-3-b3-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-3))
                            (p (rota-1-rot-3-b3-01-1-witness p)))
                 (:instance b3-0-set-a3 (p (rota-1-rot-3-b3-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-3)
                                             (rota-1-rot-3-b3-01-1-witness p))))
                 (:instance rot-3-inv*f (point (rota-1-rot-3-b3-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-3))
                            (p1 (rot-3-inv*f-witness (rota-1-rot-3-b3-01-1-witness p)))
                            (p2 (rota-1-rot-3-b3-01-1-witness p))))
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance rota-1-rot-4-b4-11 (p p))
                 (:instance rota-1-rot-4-b4-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-4)
                                    (rota-1-rot-4-b4-11-1-witness p))))
                 (:instance b4-11 (p (rota-1-rot-4-b4-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-4))
                            (p (rota-1-rot-4-b4-11-1-witness p)))
                 (:instance b3-0-set-a4 (p (rota-1-rot-4-b4-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-4)
                                             (rota-1-rot-4-b4-11-1-witness p))))
                 (:instance rot-4-inv*f (point (rota-1-rot-4-b4-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-4))
                            (p1 (rot-4-inv*f-witness (rota-1-rot-4-b4-11-1-witness p)))
                            (p2 (rota-1-rot-4-b4-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-4)
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rota-1-rot-4-b4-01 (p p))
                 (:instance rota-1-rot-4-b4-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-4)
                                    (rota-1-rot-4-b4-01-1-witness p))))
                 (:instance b4-01 (p (rota-1-rot-4-b4-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-4))
                            (p (rota-1-rot-4-b4-01-1-witness p)))
                 (:instance b3-0-set-a4 (p (rota-1-rot-4-b4-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-4)
                                             (rota-1-rot-4-b4-01-1-witness p))))
                 (:instance rot-4-inv*f (point (rota-1-rot-4-b4-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-4))
                            (p1 (rot-4-inv*f-witness (rota-1-rot-4-b4-01-1-witness p)))
                            (p2 (rota-1-rot-4-b4-01-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance rota-1-rot-5-b5-11 (p p))
                 (:instance rota-1-rot-5-b5-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-5)
                                    (rota-1-rot-5-b5-11-1-witness p))))
                 (:instance b5-11 (p (rota-1-rot-5-b5-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-5))
                            (p (rota-1-rot-5-b5-11-1-witness p)))
                 (:instance b3-0-set-a5 (p (rota-1-rot-5-b5-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-5)
                                             (rota-1-rot-5-b5-11-1-witness p))))
                 (:instance rot-5-inv*f (point (rota-1-rot-5-b5-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-5))
                            (p1 (rot-5-inv*f-witness (rota-1-rot-5-b5-11-1-witness p)))
                            (p2 (rota-1-rot-5-b5-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-5)
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rota-1-rot-5-b5-01 (p p))
                 (:instance rota-1-rot-5-b5-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-5)
                                    (rota-1-rot-5-b5-01-1-witness p))))
                 (:instance b5-01 (p (rota-1-rot-5-b5-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-5))
                            (p (rota-1-rot-5-b5-01-1-witness p)))
                 (:instance b3-0-set-a5 (p (rota-1-rot-5-b5-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-5)
                                             (rota-1-rot-5-b5-01-1-witness p))))
                 (:instance rot-5-inv*f (point (rota-1-rot-5-b5-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-5))
                            (p1 (rot-5-inv*f-witness (rota-1-rot-5-b5-01-1-witness p)))
                            (p2 (rota-1-rot-5-b5-01-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance rota-1-rot-6-b6-11 (p p))
                 (:instance rota-1-rot-6-b6-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-6)
                                    (rota-1-rot-6-b6-11-1-witness p))))
                 (:instance b6-11 (p (rota-1-rot-6-b6-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-6))
                            (p (rota-1-rot-6-b6-11-1-witness p)))
                 (:instance b3-0-set-a6 (p (rota-1-rot-6-b6-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-6)
                                             (rota-1-rot-6-b6-11-1-witness p))))
                 (:instance rot-6-inv*f (point (rota-1-rot-6-b6-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-6))
                            (p1 (rot-6-inv*f-witness (rota-1-rot-6-b6-11-1-witness p)))
                            (p2 (rota-1-rot-6-b6-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-6)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rota-1-rot-6-b6-01 (p p))
                 (:instance rota-1-rot-6-b6-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-6)
                                    (rota-1-rot-6-b6-01-1-witness p))))
                 (:instance b6-01 (p (rota-1-rot-6-b6-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-6))
                            (p (rota-1-rot-6-b6-01-1-witness p)))
                 (:instance b3-0-set-a6 (p (rota-1-rot-6-b6-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-6)
                                             (rota-1-rot-6-b6-01-1-witness p))))
                 (:instance rot-6-inv*f (point (rota-1-rot-6-b6-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-6))
                            (p1 (rot-6-inv*f-witness (rota-1-rot-6-b6-01-1-witness p)))
                            (p2 (rota-1-rot-6-b6-01-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance rota-1-rot-7-b7-11 (p p))
                 (:instance rota-1-rot-7-b7-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-7)
                                    (rota-1-rot-7-b7-11-1-witness p))))
                 (:instance b7-11 (p (rota-1-rot-7-b7-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-7))
                            (p (rota-1-rot-7-b7-11-1-witness p)))
                 (:instance b3-0-set-a7 (p (rota-1-rot-7-b7-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-7)
                                             (rota-1-rot-7-b7-11-1-witness p))))
                 (:instance rot-7-inv*f (point (rota-1-rot-7-b7-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-7))
                            (p1 (rot-7-inv*f-witness (rota-1-rot-7-b7-11-1-witness p)))
                            (p2 (rota-1-rot-7-b7-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-7)
                 (:instance rota-1-rot-7-b7-01 (p p))
                 (:instance rota-1-rot-7-b7-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-7)
                                    (rota-1-rot-7-b7-01-1-witness p))))
                 (:instance b7-01 (p (rota-1-rot-7-b7-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-7))
                            (p (rota-1-rot-7-b7-01-1-witness p)))
                 (:instance b3-0-set-a7 (p (rota-1-rot-7-b7-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-7)
                                             (rota-1-rot-7-b7-01-1-witness p))))
                 (:instance rot-7-inv*f (point (rota-1-rot-7-b7-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-7))
                            (p1 (rot-7-inv*f-witness (rota-1-rot-7-b7-01-1-witness p)))
                            (p2 (rota-1-rot-7-b7-01-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rota-1-rot-8-b8-11 (p p))
                 (:instance rota-1-rot-8-b8-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-8)
                                    (rota-1-rot-8-b8-11-1-witness p))))
                 (:instance b8-11 (p (rota-1-rot-8-b8-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-8))
                            (p (rota-1-rot-8-b8-11-1-witness p)))
                 (:instance b3-0-set-a8 (p (rota-1-rot-8-b8-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-8)
                                             (rota-1-rot-8-b8-11-1-witness p))))
                 (:instance rot-8-inv*f (point (rota-1-rot-8-b8-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-8))
                            (p1 (rot-8-inv*f-witness (rota-1-rot-8-b8-11-1-witness p)))
                            (p2 (rota-1-rot-8-b8-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-8)
                 (:instance rota-1-rot-8-b8-01 (p p))
                 (:instance rota-1-rot-8-b8-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-8)
                                    (rota-1-rot-8-b8-01-1-witness p))))
                 (:instance b8-01 (p (rota-1-rot-8-b8-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-8))
                            (p (rota-1-rot-8-b8-01-1-witness p)))
                 (:instance b3-0-set-a8 (p (rota-1-rot-8-b8-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-8)
                                             (rota-1-rot-8-b8-01-1-witness p))))
                 (:instance rot-8-inv*f (point (rota-1-rot-8-b8-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-8))
                            (p1 (rot-8-inv*f-witness (rota-1-rot-8-b8-01-1-witness p)))
                            (p2 (rota-1-rot-8-b8-01-1-witness p)))
                 )
           :in-theory nil
           )
          ))

(defun-sk rot-3-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-3)) p) point))))

(defun b3-00 (p)
  (and (b3-0-set-a3 p)
       (b3-f p)
       (rot-3-inv*b3-f p)))

(defun b3-10 (p)
  (and (b3-0-set-a3 p)
       (set-f-p p)
       (rot-3-inv*b3-f p)))

(defun-sk rot-3-b3-00-1 (point)
  (exists p
          (and (b3-00 p)
               (m-= (m-* (rot-3) p) point))))

(defun rot-3-b3-00 (p)
  (and (point-in-r3 p)
       (rot-3-b3-00-1 p)))

(defun-sk rot-3-b3-10-1 (point)
  (exists p
          (and (b3-10 p)
               (m-= (m-* (rot-3) p) point))))

(defun rot-3-b3-10 (p)
  (and (point-in-r3 p)
       (rot-3-b3-10-1 p)))

(defun-sk rot-4-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-4)) p) point))))

(defun b4-00 (p)
  (and (b3-0-set-a4 p)
       (b3-f p)
       (rot-4-inv*b3-f p)))

(defun b4-10 (p)
  (and (b3-0-set-a4 p)
       (set-f-p p)
       (rot-4-inv*b3-f p)))

(defun-sk rot-4-b4-00-1 (point)
  (exists p
          (and (b4-00 p)
               (m-= (m-* (rot-4) p) point))))

(defun rot-4-b4-00 (p)
  (and (point-in-r3 p)
       (rot-4-b4-00-1 p)))

(defun-sk rot-4-b4-10-1 (point)
  (exists p
          (and (b4-10 p)
               (m-= (m-* (rot-4) p) point))))

(defun rot-4-b4-10 (p)
  (and (point-in-r3 p)
       (rot-4-b4-10-1 p)))

(defun-sk rot-5-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-5)) p) point))))

(defun b5-00 (p)
  (and (b3-0-set-a5 p)
       (b3-f p)
       (rot-5-inv*b3-f p)))

(defun b5-10 (p)
  (and (b3-0-set-a5 p)
       (set-f-p p)
       (rot-5-inv*b3-f p)))

(defun-sk rot-5-b5-00-1 (point)
  (exists p
          (and (b5-00 p)
               (m-= (m-* (rot-5) p) point))))

(defun rot-5-b5-00 (p)
  (and (point-in-r3 p)
       (rot-5-b5-00-1 p)))

(defun-sk rot-5-b5-10-1 (point)
  (exists p
          (and (b5-10 p)
               (m-= (m-* (rot-5) p) point))))

(defun rot-5-b5-10 (p)
  (and (point-in-r3 p)
       (rot-5-b5-10-1 p)))

(defun-sk rot-6-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-6)) p) point))))

(defun b6-00 (p)
  (and (b3-0-set-a6 p)
       (b3-f p)
       (rot-6-inv*b3-f p)))

(defun b6-10 (p)
  (and (b3-0-set-a6 p)
       (set-f-p p)
       (rot-6-inv*b3-f p)))

(defun-sk rot-6-b6-00-1 (point)
  (exists p
          (and (b6-00 p)
               (m-= (m-* (rot-6) p) point))))

(defun rot-6-b6-00 (p)
  (and (point-in-r3 p)
       (rot-6-b6-00-1 p)))

(defun-sk rot-6-b6-10-1 (point)
  (exists p
          (and (b6-10 p)
               (m-= (m-* (rot-6) p) point))))

(defun rot-6-b6-10 (p)
  (and (point-in-r3 p)
       (rot-6-b6-10-1 p)))

(defun-sk rot-7-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-7)) p) point))))

(defun b7-00 (p)
  (and (b3-0-set-a7 p)
       (b3-f p)
       (rot-7-inv*b3-f p)))

(defun b7-10 (p)
  (and (b3-0-set-a7 p)
       (set-f-p p)
       (rot-7-inv*b3-f p)))

(defun-sk rot-7-b7-00-1 (point)
  (exists p
          (and (b7-00 p)
               (m-= (m-* (rot-7) p) point))))

(defun rot-7-b7-00 (p)
  (and (point-in-r3 p)
       (rot-7-b7-00-1 p)))

(defun-sk rot-7-b7-10-1 (point)
  (exists p
          (and (b7-10 p)
               (m-= (m-* (rot-7) p) point))))

(defun rot-7-b7-10 (p)
  (and (point-in-r3 p)
       (rot-7-b7-10-1 p)))

(defun-sk rot-8-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-8)) p) point))))

(defun b8-00 (p)
  (and (b3-0-set-a8 p)
       (b3-f p)
       (rot-8-inv*b3-f p)))

(defun b8-10 (p)
  (and (b3-0-set-a8 p)
       (set-f-p p)
       (rot-8-inv*b3-f p)))

(defun-sk rot-8-b8-00-1 (point)
  (exists p
          (and (b8-00 p)
               (m-= (m-* (rot-8) p) point))))

(defun rot-8-b8-00 (p)
  (and (point-in-r3 p)
       (rot-8-b8-00-1 p)))

(defun-sk rot-8-b8-10-1 (point)
  (exists p
          (and (b8-10 p)
               (m-= (m-* (rot-8) p) point))))

(defun rot-8-b8-10 (p)
  (and (point-in-r3 p)
       (rot-8-b8-10-1 p)))

(defthmd a3-a8-b3-0-n-b3-f=>
  (implies (b3-0-n-b3-f p)
           (or (rot-3-b3-00 p)
               (rot-3-b3-10 p)
               (rot-4-b4-00 p)
               (rot-4-b4-10 p)
               (rot-5-b5-00 p)
               (rot-5-b5-10 p)
               (rot-6-b6-00 p)
               (rot-6-b6-10 p)
               (rot-7-b7-00 p)
               (rot-7-b7-10 p)
               (rot-8-b8-00 p)
               (rot-8-b8-10 p)))
  :hints (("goal"
           :cases ((b3-0-a-inv-b3-0-set-a3 p)
                   (b3-0-a-inv-r-b3-0-set-a4 p)
                   (b3-0-r-1-a-inv-b3-0-set-a5 p)
                   (b3-0-r-1-a-inv-r-b3-0-set-a6 p)
                   (b3-0-set-a7 p)
                   (b3-0-set-a8 p))
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b3-0-iff-a3-to-a8 (p p))
                 )
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance b3-0-a-inv-b3-0-set-a3 (p p))
                 (:instance b3-0-a-inv-b3-0-set-a3-1 (p p))
                 (:instance rot-3-b3-10 (p p))
                 (:instance rot-3-b3-10-1-suff (point p) (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance b3-10 (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance b3-f (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance rot-3-b3-00 (p p))
                 (:instance rot-3-b3-00-1-suff (point p) (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance b3-00 (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance rot-3)
                 (:instance rot-3-inv*b3-f-suff (p p) (point (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-3))
                            (m2 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-3)))
                            (m5 (id-rotation))
                            (m6 (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance m-*point-id=point (p1 (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance b3-0-set-a3 (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance m-*-m-inverse-m
                            (m (rot-3)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (a-inv-rotation (acl2-sqrt 2))))
                 (:instance b3 (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance b3-0-a-inv-r-b3-0-set-a4 (p p))
                 (:instance b3-0-a-inv-r-b3-0-set-a4-1 (p p))
                 (:instance rot-4-b4-10 (p p))
                 (:instance rot-4-b4-10-1-suff (point p) (p (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance b4-10 (p (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance b3-f (p (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance rot-4-b4-00 (p p))
                 (:instance rot-4-b4-00-1-suff (point p) (p (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance b4-00 (p (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance rot-4)
                 (:instance rot-4-inv*b3-f-suff (p p) (point (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-4))
                            (m2 (b3-0-a-inv-r-b3-0-set-a4-1-witness p))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-4)))
                            (m5 (id-rotation))
                            (m6 (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance associativity-of-m-*
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (m3 (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance m-*point-id=point (p1 (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance b3-0-set-a4 (p (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance m-*-m-inverse-m
                            (m (rot-4)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance r3-rotationp (m (rot-4)))
                 (:instance b3 (p (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance b3-0-r-1-a-inv-b3-0-set-a5 (p p))
                 (:instance b3-0-r-1-a-inv-b3-0-set-a5-1 (p p))
                 (:instance rot-5-b5-10 (p p))
                 (:instance rot-5-b5-10-1-suff (point p) (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance b5-10 (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance b3-f (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance rot-5-b5-00 (p p))
                 (:instance rot-5-b5-00-1-suff (point p) (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance b5-00 (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance rot-5)
                 (:instance rot-5-inv*b3-f-suff (p p) (point (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-5))
                            (m2 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-5)))
                            (m5 (id-rotation))
                            (m6 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance associativity-of-m-*
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance m-*point-id=point (p1 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance b3-0-set-a5 (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance m-*-m-inverse-m
                            (m (rot-5)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance r3-rotationp (m (rot-5)))
                 (:instance b3 (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance b3-0-r-1-a-inv-r-b3-0-set-a6 (p p))
                 (:instance b3-0-r-1-a-inv-r-b3-0-set-a6-1 (p p))
                 (:instance rot-6-b6-10 (p p))
                 (:instance rot-6-b6-10-1-suff (point p) (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance b6-10 (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance b3-f (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance rot-6-b6-00 (p p))
                 (:instance rot-6-b6-00-1-suff (point p) (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance b6-00 (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance rot-6)
                 (:instance rot-6-inv*b3-f-suff (p p) (point (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-6))
                            (m2 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-6)))
                            (m5 (id-rotation))
                            (m6 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>sub-3
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (m4 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance m-*point-id=point (p1 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance b3-0-set-a6 (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance m-*-m-inverse-m
                            (m (rot-6)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance r3-rotationp (m (rot-6)))
                 (:instance b3 (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance rot-7-b7-10 (p p))
                 (:instance rot-7-b7-10-1-suff (point p) (p p))
                 (:instance b7-10 (p p))
                 (:instance b3-f (p p))
                 (:instance b3-0-set-a7 (p p))
                 (:instance rot-7-b7-00 (p p))
                 (:instance rot-7-b7-00-1-suff (point p) (p p))
                 (:instance b7-00 (p p))
                 (:instance rot-7)
                 (:instance rot-7-inv*b3-f-suff (p p) (point p))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-7))
                            (m2 p)
                            (m3 p)
                            (m4 (r3-m-inverse (rot-7)))
                            (m5 (id-rotation))
                            (m6 p))
                 (:instance m-*point-id=point (p1 p))
                 (:instance m-*-m-inverse-m
                            (m (rot-7)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (id-rotation)))
                 )
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rot-8-b8-10 (p p))
                 (:instance rot-8-b8-10-1-suff (point p) (p p))
                 (:instance b8-10 (p p))
                 (:instance b3-f (p p))
                 (:instance b3-0-set-a8 (p p))
                 (:instance rot-8-b8-00 (p p))
                 (:instance rot-8-b8-00-1-suff (point p) (p p))
                 (:instance b8-00 (p p))
                 (:instance rot-8)
                 (:instance rot-8-inv*b3-f-suff (p p) (point p))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-8))
                            (m2 p)
                            (m3 p)
                            (m4 (r3-m-inverse (rot-8)))
                            (m5 (id-rotation))
                            (m6 p))
                 (:instance m-*point-id=point (p1 p))
                 (:instance m-*-m-inverse-m
                            (m (rot-8)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (id-rotation)))
                 )
           :in-theory nil
           )
          ))

(defthmd rot-3-8-b-3-8-01-or-11=>1-1
  (implies (and (m-= (m-* m1 m2) m3)
                (m-= (m-* m4 m5) m2))
           (m-= (m-* (m-* m1 m4) m5) m3)))

(defthmd rot-3-8-b-3-8-01-or-11=>1-2
  (implies (and (m-= (m-* m1 m2) m3)
                (m-= (m-* m1 m2 m4) m5)
                (m-= (m-* m3 m4) m6))
           (m-= m6 m5)))

(defthmd rot-3-8-b-3-8-01-or-11=>1
  (implies (and (r3-rotationp rot)
                (set-f-p p)
                (point-in-r3 wit-wit)
                (m-= (m-* rot wit) p)
                (m-= (m-* (r3-m-inverse rot) wit-wit) wit))
           (set-f-p wit-wit))
  :hints (("goal"
           :use ((:instance associativity-of-m-*-1
                            (m1 rot)
                            (m2 (r3-m-inverse rot))
                            (m3 wit-wit))
                 (:instance m-*-m-m-inverse
                            (m rot))
                 (:instance r3-rotationp (m rot))
                 (:instance m-*point-id=point
                            (p1 wit-wit))
                 (:instance rota-1-rota-f-iff-set-f-p-2-1
                            (p2 wit-wit)
                            (p1 p))
                 (:instance set-f-p (point wit-wit))
                 (:instance rot-3-8-b-3-8-01-or-11=>1-1
                            (m1 rot)
                            (m2 wit)
                            (m3 p)
                            (m4 (r3-m-inverse rot))
                            (m5 wit-wit))
                 (:instance rot-3-8-b-3-8-01-or-11=>1-2
                            (m1 rot)
                            (m2 (r3-m-inverse rot))
                            (m3 (id-rotation))
                            (m4 wit-wit)
                            (m5 p)
                            (m6 wit-wit))
                 )
           :in-theory nil

           )))

(defthmd rot-3-8-b-3-8-01-or-11=>
  (implies (or (rot-3-b3-00 p)
               (rot-3-b3-10 p)
               (rot-4-b4-00 p)
               (rot-4-b4-10 p)
               (rot-5-b5-00 p)
               (rot-5-b5-10 p)
               (rot-6-b6-00 p)
               (rot-6-b6-10 p)
               (rot-7-b7-00 p)
               (rot-7-b7-10 p)
               (rot-8-b8-00 p)
               (rot-8-b8-10 p))
           (b3-0-n-b3-f p))
  :hints (("goal"
           :cases ((rot-3-b3-00 p)
                   (rot-3-b3-10 p)
                   (rot-4-b4-00 p)
                   (rot-4-b4-10 p)
                   (rot-5-b5-00 p)
                   (rot-5-b5-10 p)
                   (rot-6-b6-00 p)
                   (rot-6-b6-10 p)
                   (rot-7-b7-00 p)
                   (rot-7-b7-10 p)
                   (rot-8-b8-00 p)
                   (rot-8-b8-10 p)
                   )
           :in-theory nil
           )
          ("subgoal 12"
           :use ((:instance rot-3-b3-00 (p p))
                 (:instance rot-3-b3-00-1 (point p))
                 (:instance b3-00 (p (rot-3-b3-00-1-witness p)))
                 (:instance rot-3-inv*b3-f (point (rot-3-b3-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-3-b3-00-1-witness p))
                            (rot (rot-3)))
                 (:instance rot-3)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-3) (rot-3-b3-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-3) (rot-3-b3-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-3))
                            (wit (rot-3-b3-00-1-witness p))
                            (p p)
                            (wit-wit (rot-3-inv*b3-f-witness (rot-3-b3-00-1-witness p))))
                 (:instance b3 (p (rot-3-inv*b3-f-witness (rot-3-b3-00-1-witness p))))
                 (:instance b3-f (p (rot-3-inv*b3-f-witness (rot-3-b3-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 11"
           :use ((:instance rot-3-b3-10 (p p))
                 (:instance rot-3-b3-10-1 (point p))
                 (:instance b3-10 (p (rot-3-b3-10-1-witness p)))
                 (:instance rot-3-inv*b3-f (point (rot-3-b3-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-3-b3-10-1-witness p))
                            (rot (rot-3)))
                 (:instance rot-3)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-3) (rot-3-b3-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-3) (rot-3-b3-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-3))
                            (wit (rot-3-b3-10-1-witness p))
                            (p p)
                            (wit-wit (rot-3-inv*b3-f-witness (rot-3-b3-10-1-witness p))))
                 (:instance b3 (p (rot-3-inv*b3-f-witness (rot-3-b3-10-1-witness p))))
                 (:instance b3-f (p (rot-3-inv*b3-f-witness (rot-3-b3-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 10"
           :use ((:instance rot-4-b4-00 (p p))
                 (:instance rot-4-b4-00-1 (point p))
                 (:instance b4-00 (p (rot-4-b4-00-1-witness p)))
                 (:instance rot-4-inv*b3-f (point (rot-4-b4-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-4-b4-00-1-witness p))
                            (rot (rot-4)))
                 (:instance rot-4)
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-4) (rot-4-b4-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-4) (rot-4-b4-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-4))
                            (wit (rot-4-b4-00-1-witness p))
                            (p p)
                            (wit-wit (rot-4-inv*b3-f-witness (rot-4-b4-00-1-witness p))))
                 (:instance b3 (p (rot-4-inv*b3-f-witness (rot-4-b4-00-1-witness p))))
                 (:instance b3-f (p (rot-4-inv*b3-f-witness (rot-4-b4-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 9"
           :use ((:instance rot-4-b4-10 (p p))
                 (:instance rot-4-b4-10-1 (point p))
                 (:instance b4-10 (p (rot-4-b4-10-1-witness p)))
                 (:instance rot-4-inv*b3-f (point (rot-4-b4-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-4-b4-10-1-witness p))
                            (rot (rot-4)))
                 (:instance rot-4)
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-4) (rot-4-b4-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-4) (rot-4-b4-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-4))
                            (wit (rot-4-b4-10-1-witness p))
                            (p p)
                            (wit-wit (rot-4-inv*b3-f-witness (rot-4-b4-10-1-witness p))))
                 (:instance b3 (p (rot-4-inv*b3-f-witness (rot-4-b4-10-1-witness p))))
                 (:instance b3-f (p (rot-4-inv*b3-f-witness (rot-4-b4-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 8"
           :use ((:instance rot-5-b5-00 (p p))
                 (:instance rot-5-b5-00-1 (point p))
                 (:instance b5-00 (p (rot-5-b5-00-1-witness p)))
                 (:instance rot-5-inv*b3-f (point (rot-5-b5-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-5-b5-00-1-witness p))
                            (rot (rot-5)))
                 (:instance rot-5)
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-5) (rot-5-b5-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-5) (rot-5-b5-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-5))
                            (wit (rot-5-b5-00-1-witness p))
                            (p p)
                            (wit-wit (rot-5-inv*b3-f-witness (rot-5-b5-00-1-witness p))))
                 (:instance b3 (p (rot-5-inv*b3-f-witness (rot-5-b5-00-1-witness p))))
                 (:instance b3-f (p (rot-5-inv*b3-f-witness (rot-5-b5-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 7"
           :use ((:instance rot-5-b5-10 (p p))
                 (:instance rot-5-b5-10-1 (point p))
                 (:instance b5-10 (p (rot-5-b5-10-1-witness p)))
                 (:instance rot-5-inv*b3-f (point (rot-5-b5-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-5-b5-10-1-witness p))
                            (rot (rot-5)))
                 (:instance rot-5)
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-5) (rot-5-b5-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-5) (rot-5-b5-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-5))
                            (wit (rot-5-b5-10-1-witness p))
                            (p p)
                            (wit-wit (rot-5-inv*b3-f-witness (rot-5-b5-10-1-witness p))))
                 (:instance b3 (p (rot-5-inv*b3-f-witness (rot-5-b5-10-1-witness p))))
                 (:instance b3-f (p (rot-5-inv*b3-f-witness (rot-5-b5-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance rot-6-b6-00 (p p))
                 (:instance rot-6-b6-00-1 (point p))
                 (:instance b6-00 (p (rot-6-b6-00-1-witness p)))
                 (:instance rot-6-inv*b3-f (point (rot-6-b6-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-6-b6-00-1-witness p))
                            (rot (rot-6)))
                 (:instance rot-6)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-6) (rot-6-b6-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-6) (rot-6-b6-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-6))
                            (wit (rot-6-b6-00-1-witness p))
                            (p p)
                            (wit-wit (rot-6-inv*b3-f-witness (rot-6-b6-00-1-witness p))))
                 (:instance b3 (p (rot-6-inv*b3-f-witness (rot-6-b6-00-1-witness p))))
                 (:instance b3-f (p (rot-6-inv*b3-f-witness (rot-6-b6-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance rot-6-b6-10 (p p))
                 (:instance rot-6-b6-10-1 (point p))
                 (:instance b6-10 (p (rot-6-b6-10-1-witness p)))
                 (:instance rot-6-inv*b3-f (point (rot-6-b6-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-6-b6-10-1-witness p))
                            (rot (rot-6)))
                 (:instance rot-6)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-6) (rot-6-b6-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-6) (rot-6-b6-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-6))
                            (wit (rot-6-b6-10-1-witness p))
                            (p p)
                            (wit-wit (rot-6-inv*b3-f-witness (rot-6-b6-10-1-witness p))))
                 (:instance b3 (p (rot-6-inv*b3-f-witness (rot-6-b6-10-1-witness p))))
                 (:instance b3-f (p (rot-6-inv*b3-f-witness (rot-6-b6-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance rot-7-b7-00 (p p))
                 (:instance rot-7-b7-00-1 (point p))
                 (:instance b7-00 (p (rot-7-b7-00-1-witness p)))
                 (:instance rot-7-inv*b3-f (point (rot-7-b7-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-7-b7-00-1-witness p))
                            (rot (rot-7)))
                 (:instance rot-7)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-7) (rot-7-b7-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-7) (rot-7-b7-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-7))
                            (wit (rot-7-b7-00-1-witness p))
                            (p p)
                            (wit-wit (rot-7-inv*b3-f-witness (rot-7-b7-00-1-witness p))))
                 (:instance b3 (p (rot-7-inv*b3-f-witness (rot-7-b7-00-1-witness p))))
                 (:instance b3-f (p (rot-7-inv*b3-f-witness (rot-7-b7-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance rot-7-b7-10 (p p))
                 (:instance rot-7-b7-10-1 (point p))
                 (:instance b7-10 (p (rot-7-b7-10-1-witness p)))
                 (:instance rot-7-inv*b3-f (point (rot-7-b7-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-7-b7-10-1-witness p))
                            (rot (rot-7)))
                 (:instance rot-7)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-7) (rot-7-b7-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-7) (rot-7-b7-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-7))
                            (wit (rot-7-b7-10-1-witness p))
                            (p p)
                            (wit-wit (rot-7-inv*b3-f-witness (rot-7-b7-10-1-witness p))))
                 (:instance b3 (p (rot-7-inv*b3-f-witness (rot-7-b7-10-1-witness p))))
                 (:instance b3-f (p (rot-7-inv*b3-f-witness (rot-7-b7-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance rot-8-b8-00 (p p))
                 (:instance rot-8-b8-00-1 (point p))
                 (:instance b8-00 (p (rot-8-b8-00-1-witness p)))
                 (:instance rot-8-inv*b3-f (point (rot-8-b8-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-8-b8-00-1-witness p))
                            (rot (rot-8)))
                 (:instance rot-8)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-8) (rot-8-b8-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-8) (rot-8-b8-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-8))
                            (wit (rot-8-b8-00-1-witness p))
                            (p p)
                            (wit-wit (rot-8-inv*b3-f-witness (rot-8-b8-00-1-witness p))))
                 (:instance b3 (p (rot-8-inv*b3-f-witness (rot-8-b8-00-1-witness p))))
                 (:instance b3-f (p (rot-8-inv*b3-f-witness (rot-8-b8-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rot-8-b8-10 (p p))
                 (:instance rot-8-b8-10-1 (point p))
                 (:instance b8-10 (p (rot-8-b8-10-1-witness p)))
                 (:instance rot-8-inv*b3-f (point (rot-8-b8-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-8-b8-10-1-witness p))
                            (rot (rot-8)))
                 (:instance rot-8)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-8) (rot-8-b8-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-8) (rot-8-b8-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-8))
                            (wit (rot-8-b8-10-1-witness p))
                            (p p)
                            (wit-wit (rot-8-inv*b3-f-witness (rot-8-b8-10-1-witness p))))
                 (:instance b3 (p (rot-8-inv*b3-f-witness (rot-8-b8-10-1-witness p))))
                 (:instance b3-f (p (rot-8-inv*b3-f-witness (rot-8-b8-10-1-witness p))))
                 )
           :in-theory nil
           )
          ))

(defun rot-9 ()
  (b-inv-rotation (acl2-sqrt 2)))

(defun rot-10 ()
  (m-* (b-inv-rotation (acl2-sqrt 2))
       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

(defun rot-11 ()
  (m-* (rotation-3d
        (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
       (b-inv-rotation (acl2-sqrt 2))))

(defun rot-12 ()
  (m-* (rotation-3d
        (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
       (b-inv-rotation (acl2-sqrt 2))
       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))

(defun rot-13 ()
  (id-rotation))

(defun rot-14 ()
  (id-rotation))

(defun-sk rot-9-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-9)) p) point))))

(defun b9-01 (p)
  (and (b3-0-set-a9 p)
       (b3-f p)
       (rot-9-inv*f p)))

(defun b9-11 (p)
  (and (b3-0-set-a9 p)
       (set-f-p p)
       (rot-9-inv*f p)))

(defun-sk rota-1-rot-9-b9-01-1 (point)
  (exists p
          (and (b9-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-9) p))
                    point))))

(defun rota-1-rot-9-b9-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-9-b9-01-1 p)))

(defun-sk rota-1-rot-9-b9-11-1 (point)
  (exists p
          (and (b9-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-9) p))
                    point))))

(defun rota-1-rot-9-b9-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-9-b9-11-1 p)))

(defun-sk rot-10-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-10)) p) point))))

(defun b10-01 (p)
  (and (b3-0-set-a10 p)
       (b3-f p)
       (rot-10-inv*f p)))

(defun b10-11 (p)
  (and (b3-0-set-a10 p)
       (set-f-p p)
       (rot-10-inv*f p)))

(defun-sk rota-1-rot-10-b10-01-1 (point)
  (exists p
          (and (b10-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-10) p))
                    point))))

(defun rota-1-rot-10-b10-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-10-b10-01-1 p)))

(defun-sk rota-1-rot-10-b10-11-1 (point)
  (exists p
          (and (b10-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-10) p))
                    point))))

(defun rota-1-rot-10-b10-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-10-b10-11-1 p)))

(defun-sk rot-11-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-11)) p) point))))

(defun b11-01 (p)
  (and (b3-0-set-a11 p)
       (b3-f p)
       (rot-11-inv*f p)))

(defun b11-11 (p)
  (and (b3-0-set-a11 p)
       (set-f-p p)
       (rot-11-inv*f p)))

(defun-sk rota-1-rot-11-b11-01-1 (point)
  (exists p
          (and (b11-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-11) p))
                    point))))

(defun rota-1-rot-11-b11-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-11-b11-01-1 p)))

(defun-sk rota-1-rot-11-b11-11-1 (point)
  (exists p
          (and (b11-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-11) p))
                    point))))

(defun rota-1-rot-11-b11-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-11-b11-11-1 p)))

(defun-sk rot-12-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-12)) p) point))))

(defun b12-01 (p)
  (and (b3-0-set-a12 p)
       (b3-f p)
       (rot-12-inv*f p)))

(defun b12-11 (p)
  (and (b3-0-set-a12 p)
       (set-f-p p)
       (rot-12-inv*f p)))

(defun-sk rota-1-rot-12-b12-01-1 (point)
  (exists p
          (and (b12-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-12) p))
                    point))))

(defun rota-1-rot-12-b12-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-12-b12-01-1 p)))

(defun-sk rota-1-rot-12-b12-11-1 (point)
  (exists p
          (and (b12-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-12) p))
                    point))))

(defun rota-1-rot-12-b12-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-12-b12-11-1 p)))

(defun-sk rot-13-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-13)) p) point))))

(defun b13-01 (p)
  (and (b3-0-set-a13 p)
       (b3-f p)
       (rot-13-inv*f p)))

(defun b13-11 (p)
  (and (b3-0-set-a13 p)
       (set-f-p p)
       (rot-13-inv*f p)))

(defun-sk rota-1-rot-13-b13-01-1 (point)
  (exists p
          (and (b13-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-13) p))
                    point))))

(defun rota-1-rot-13-b13-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-13-b13-01-1 p)))

(defun-sk rota-1-rot-13-b13-11-1 (point)
  (exists p
          (and (b13-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-13) p))
                    point))))

(defun rota-1-rot-13-b13-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-13-b13-11-1 p)))

(defun-sk rot-14-inv*f (point)
  (exists p
          (and (set-f-p p)
               (m-= (m-* (r3-m-inverse (rot-14)) p) point))))

(defun b14-01 (p)
  (and (b3-0-set-a14 p)
       (b3-f p)
       (rot-14-inv*f p)))

(defun b14-11 (p)
  (and (b3-0-set-a14 p)
       (set-f-p p)
       (rot-14-inv*f p)))

(defun-sk rota-1-rot-14-b14-01-1 (point)
  (exists p
          (and (b14-01 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-14) p))
                    point))))

(defun rota-1-rot-14-b14-01 (p)
  (and (point-in-r3 p)
       (rota-1-rot-14-b14-01-1 p)))

(defun-sk rota-1-rot-14-b14-11-1 (point)
  (exists p
          (and (b14-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p)
                                                   (m-* (rot-14) p))
                    point))))

(defun rota-1-rot-14-b14-11 (p)
  (and (point-in-r3 p)
       (rota-1-rot-14-b14-11-1 p)))

(defthmd a9-a14-rot-a-inv-b3-0-nf=>
  (implies (rota-inv-b3-0-n-f p)
           (or (rota-1-rot-9-b9-11 p)
               (rota-1-rot-9-b9-01 p)
               (rota-1-rot-10-b10-11 p)
               (rota-1-rot-10-b10-01 p)
               (rota-1-rot-11-b11-11 p)
               (rota-1-rot-11-b11-01 p)
               (rota-1-rot-12-b12-11 p)
               (rota-1-rot-12-b12-01 p)
               (rota-1-rot-13-b13-11 p)
               (rota-1-rot-13-b13-01 p)
               (rota-1-rot-14-b14-11 p)
               (rota-1-rot-14-b14-01 p)))
  :hints (("goal"
           :cases ((b3-0-b-inv-b3-0-set-a9 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-b-inv-r-b3-0-set-a10 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-r-1-b-inv-b3-0-set-a11 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-r-1-b-inv-r-b3-0-set-a12 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a13 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a14 (rota-inv-b3-0-n-f-1-witness p)))
           :use ((:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1 (point p))
                 (:instance b3-0-n-f (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3-0-iff-a9-to-a14 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 6"
           :use((:instance b3-0-b-inv-b3-0-set-a9 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-b-inv-b3-0-set-a9-1 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-9-b9-01 (p p))
                (:instance rota-1-rot-9-b9-11 (p p))
                (:instance rota-1-rot-9-b9-01-1-suff
                           (point p)
                           (p (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b9-01
                           (p (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rota-1-rot-9-b9-11-1-suff
                           (point p)
                           (p (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b9-11
                           (p (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-f
                           (p (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0-iff-a1-to-a14
                           (p (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0
                           (p (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3 (p (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rot-9-inv*f-suff
                           (point (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-9)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-9))
                           (m2 (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-9)))
                           (m5 (id-rotation))
                           (m6 (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance m-*-m-inverse-m
                           (m (rot-9)))
                (:instance m-*point-id=point
                           (p1 (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (b-inv-rotation (acl2-sqrt 2))))
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-9)
                                    (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (b3-0-b-inv-b3-0-set-a9-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (rot (rot-9)))
                )
           :in-theory nil
           )
          ("subgoal 5"
           :use((:instance b3-0-b-inv-r-b3-0-set-a10 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-b-inv-r-b3-0-set-a10-1 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-10-b10-01 (p p))
                (:instance rota-1-rot-10-b10-11 (p p))
                (:instance rota-1-rot-10-b10-01-1-suff
                           (point p)
                           (p (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b10-01
                           (p (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rota-1-rot-10-b10-11-1-suff
                           (point p)
                           (p (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b10-11
                           (p (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-f
                           (p (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0-iff-a1-to-a14
                           (p (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0
                           (p (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rot-10-inv*f-suff
                           (point (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-10)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-10))
                           (m2 (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-10)))
                           (m5 (id-rotation))
                           (m6 (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance associativity-of-m-*
                           (m1 (b-inv-rotation (acl2-sqrt 2)))
                           (m2 (rotation-3d
                                (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                (point-on-s2-not-d)))
                           (m3 (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance m-*-m-inverse-m
                           (m (rot-10)))
                (:instance rot*rot-is-rot
                           (m1 (b-inv-rotation (acl2-sqrt 2)))
                           (m2 (rotation-3d
                                (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                (point-on-s2-not-d))))
                (:instance m-*point-id=point
                           (p1 (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (rot-10)))
                (:instance r3-rotationp-r-theta
                           (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                (:instance witness-not-in-angle-sequence)
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-10)
                                    (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (b3-0-b-inv-r-b3-0-set-a10-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (rot (rot-10)))
                )
           :in-theory nil
           )
          ("subgoal 4"
           :use((:instance b3-0-r-1-b-inv-b3-0-set-a11 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-r-1-b-inv-b3-0-set-a11-1 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-11-b11-01 (p p))
                (:instance rota-1-rot-11-b11-11 (p p))
                (:instance rota-1-rot-11-b11-01-1-suff
                           (point p)
                           (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b11-01
                           (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rota-1-rot-11-b11-11-1-suff
                           (point p)
                           (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b11-11
                           (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-f
                           (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0-iff-a1-to-a14
                           (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0
                           (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rot-11-inv*f-suff
                           (point (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-11)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-11))
                           (m2 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-11)))
                           (m5 (id-rotation))
                           (m6 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance associativity-of-m-*
                           (m2 (b-inv-rotation (acl2-sqrt 2)))
                           (m1 (rotation-3d
                                (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                (point-on-s2-not-d)))
                           (m3 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance m-*-m-inverse-m
                           (m (rot-11)))
                (:instance rot*rot-is-rot
                           (m2 (b-inv-rotation (acl2-sqrt 2)))
                           (m1 (rotation-3d
                                (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                (point-on-s2-not-d))))
                (:instance m-*point-id=point
                           (p1 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (rot-11)))
                (:instance r3-rotationp-r-theta
                           (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                (:instance witness-not-in-angle-sequence)
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-11)
                                    (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (rot (rot-11)))
                )
           :in-theory nil
           )
          ("subgoal 3"
           :use((:instance b3-0-r-1-b-inv-r-b3-0-set-a12 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-r-1-b-inv-r-b3-0-set-a12-1 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-12-b12-01 (p p))
                (:instance rota-1-rot-12-b12-11 (p p))
                (:instance rota-1-rot-12-b12-01-1-suff
                           (point p)
                           (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b12-01
                           (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rota-1-rot-12-b12-11-1-suff
                           (point p)
                           (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b12-11
                           (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-f
                           (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0-iff-a1-to-a14
                           (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3-0
                           (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance b3 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance rot-12-inv*f-suff
                           (point (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-12)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-12))
                           (m2 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-12)))
                           (m5 (id-rotation))
                           (m6 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance associativity-of-m-*
                           (m2 (b-inv-rotation (acl2-sqrt 2)))
                           (m1 (rotation-3d
                                (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                (point-on-s2-not-d)))
                           (m3 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness
                                (rota-inv-b3-0-n-f-1-witness p))))
                (:instance a3-a8-rot-a-inv-b3-0-nf=>sub-3
                           (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                0 (* 2 (acl2-pi))))
                                            (point-on-s2-not-d)))
                           (m2 (b-inv-rotation (acl2-sqrt 2)))
                           (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                           (m4 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness
                                (rota-inv-b3-0-n-f-1-witness p))))
                (:instance m-*-m-inverse-m
                           (m (rot-12)))
                (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                           (m2 (b-inv-rotation (acl2-sqrt 2)))
                           (m1 (rotation-3d
                                (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                (point-on-s2-not-d)))
                           (m3 (rotation-3d
                                (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                (point-on-s2-not-d))))
                (:instance m-*point-id=point
                           (p1 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (rot-12)))
                (:instance r3-rotationp-r-theta
                           (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                (:instance r3-rotationp-r-theta
                           (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                (:instance witness-not-in-angle-sequence)
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-12)
                                    (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p))))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness (rota-inv-b3-0-n-f-1-witness p)))
                           (rot (rot-12)))
                )
           :in-theory nil
           )
          ("subgoal 2"
           :use((:instance b3-0-set-a13 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-13-b13-01 (p p))
                (:instance rota-1-rot-13-b13-11 (p p))
                (:instance rota-1-rot-13-b13-01-1-suff
                           (point p)
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b13-01
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-13-b13-11-1-suff
                           (point p)
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b13-11
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-f
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-iff-a1-to-a14
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-13-inv*f-suff
                           (point (rota-inv-b3-0-n-f-1-witness p))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-13)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-13))
                           (m2 (rota-inv-b3-0-n-f-1-witness p))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-13)))
                           (m5 (id-rotation))
                           (m6 (rota-inv-b3-0-n-f-1-witness p)))
                (:instance m-*-m-inverse-m
                           (m (rot-13)))
                (:instance m-*point-id=point
                           (p1 (rota-inv-b3-0-n-f-1-witness p)))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (id-rotation)))
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-13)
                                    (rota-inv-b3-0-n-f-1-witness p)))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (rota-inv-b3-0-n-f-1-witness p))
                           (rot (rot-13)))
                )
           :in-theory nil
           )
          ("subgoal 1"
           :use((:instance b3-0-set-a14 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-14-b14-01 (p p))
                (:instance rota-1-rot-14-b14-11 (p p))
                (:instance rota-1-rot-14-b14-01-1-suff
                           (point p)
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b14-01
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rota-1-rot-14-b14-11-1-suff
                           (point p)
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b14-11
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-f
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0-iff-a1-to-a14
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3-0
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-14-inv*f-suff
                           (point (rota-inv-b3-0-n-f-1-witness p))
                           (p (rota-inv-b3-0-n-f-1-witness p)))
                (:instance rot-14)
                (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                           (m1 (rot-14))
                           (m2 (rota-inv-b3-0-n-f-1-witness p))
                           (m3 (rota-inv-b3-0-n-f-1-witness p))
                           (m4 (r3-m-inverse (rot-14)))
                           (m5 (id-rotation))
                           (m6 (rota-inv-b3-0-n-f-1-witness p)))
                (:instance m-*-m-inverse-m
                           (m (rot-14)))
                (:instance m-*point-id=point
                           (p1 (rota-inv-b3-0-n-f-1-witness p)))
                (:instance base-rotations
                           (x (acl2-sqrt 2)))
                (:instance r3-rotationp (m (id-rotation)))
                (:instance rotation-about-arbitrary-line=>1
                           (p1 (m-* (rot-14)
                                    (rota-inv-b3-0-n-f-1-witness p)))
                           (p2 (rota-inv-b3-0-n-f-1-witness p))
                           (angle (- (angle-const)))
                           (m (m-p))
                           (n (n-p)))
                (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                           (p1 (rota-inv-b3-0-n-f-1-witness p))
                           (rot (rot-14)))
                )
           :in-theory nil
           )
          ))

(defthmd rota-1-rot-9-14-b-9-14-01-or-11=>
  (implies (or (rota-1-rot-9-b9-11 p)
               (rota-1-rot-9-b9-01 p)
               (rota-1-rot-10-b10-11 p)
               (rota-1-rot-10-b10-01 p)
               (rota-1-rot-11-b11-11 p)
               (rota-1-rot-11-b11-01 p)
               (rota-1-rot-12-b12-11 p)
               (rota-1-rot-12-b12-01 p)
               (rota-1-rot-13-b13-11 p)
               (rota-1-rot-13-b13-01 p)
               (rota-1-rot-14-b14-11 p)
               (rota-1-rot-14-b14-01 p))
           (rota-inv-b3-0-n-f p))
  :hints (("goal"
           :cases ((or (rota-1-rot-9-b9-11 p)
                       (rota-1-rot-9-b9-01 p))
                   (or (rota-1-rot-10-b10-11 p)
                       (rota-1-rot-10-b10-01 p))
                   (or (rota-1-rot-11-b11-11 p)
                       (rota-1-rot-11-b11-01 p))
                   (or (rota-1-rot-12-b12-11 p)
                       (rota-1-rot-12-b12-01 p))
                   (or (rota-1-rot-13-b13-11 p)
                       (rota-1-rot-13-b13-01 p))
                   (or (rota-1-rot-14-b14-11 p)
                       (rota-1-rot-14-b14-01 p)))
           :in-theory nil)
          ("subgoal 6"
           :use ((:instance rota-1-rot-9-b9-11 (p p))
                 (:instance rota-1-rot-9-b9-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-9)
                                    (rota-1-rot-9-b9-11-1-witness p))))
                 (:instance b9-11 (p (rota-1-rot-9-b9-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-9))
                            (p (rota-1-rot-9-b9-11-1-witness p)))
                 (:instance b3-0-set-a9 (p (rota-1-rot-9-b9-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-9)
                                             (rota-1-rot-9-b9-11-1-witness p))))
                 (:instance rot-9-inv*f (point (rota-1-rot-9-b9-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-9))
                            (p1 (rot-9-inv*f-witness (rota-1-rot-9-b9-11-1-witness p)))
                            (p2 (rota-1-rot-9-b9-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-9)
                 (:instance rota-1-rot-9-b9-01 (p p))
                 (:instance rota-1-rot-9-b9-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-9)
                                    (rota-1-rot-9-b9-01-1-witness p))))
                 (:instance b9-01 (p (rota-1-rot-9-b9-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-9))
                            (p (rota-1-rot-9-b9-01-1-witness p)))
                 (:instance b3-0-set-a9 (p (rota-1-rot-9-b9-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-9)
                                             (rota-1-rot-9-b9-01-1-witness p))))
                 (:instance rot-9-inv*f (point (rota-1-rot-9-b9-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-9))
                            (p1 (rot-9-inv*f-witness (rota-1-rot-9-b9-01-1-witness p)))
                            (p2 (rota-1-rot-9-b9-01-1-witness p))))
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance rota-1-rot-10-b10-11 (p p))
                 (:instance rota-1-rot-10-b10-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-10)
                                    (rota-1-rot-10-b10-11-1-witness p))))
                 (:instance b10-11 (p (rota-1-rot-10-b10-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-10))
                            (p (rota-1-rot-10-b10-11-1-witness p)))
                 (:instance b3-0-set-a10 (p (rota-1-rot-10-b10-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-10)
                                             (rota-1-rot-10-b10-11-1-witness p))))
                 (:instance rot-10-inv*f (point (rota-1-rot-10-b10-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-10))
                            (p1 (rot-10-inv*f-witness (rota-1-rot-10-b10-11-1-witness p)))
                            (p2 (rota-1-rot-10-b10-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-10)
                 (:instance rot*rot-is-rot
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rota-1-rot-10-b10-01 (p p))
                 (:instance rota-1-rot-10-b10-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-10)
                                    (rota-1-rot-10-b10-01-1-witness p))))
                 (:instance b10-01 (p (rota-1-rot-10-b10-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-10))
                            (p (rota-1-rot-10-b10-01-1-witness p)))
                 (:instance b3-0-set-a10 (p (rota-1-rot-10-b10-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-10)
                                             (rota-1-rot-10-b10-01-1-witness p))))
                 (:instance rot-10-inv*f (point (rota-1-rot-10-b10-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-10))
                            (p1 (rot-10-inv*f-witness (rota-1-rot-10-b10-01-1-witness p)))
                            (p2 (rota-1-rot-10-b10-01-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance rota-1-rot-11-b11-11 (p p))
                 (:instance rota-1-rot-11-b11-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-11)
                                    (rota-1-rot-11-b11-11-1-witness p))))
                 (:instance b11-11 (p (rota-1-rot-11-b11-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-11))
                            (p (rota-1-rot-11-b11-11-1-witness p)))
                 (:instance b3-0-set-a11 (p (rota-1-rot-11-b11-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-11)
                                             (rota-1-rot-11-b11-11-1-witness p))))
                 (:instance rot-11-inv*f (point (rota-1-rot-11-b11-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-11))
                            (p1 (rot-11-inv*f-witness (rota-1-rot-11-b11-11-1-witness p)))
                            (p2 (rota-1-rot-11-b11-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-11)
                 (:instance rot*rot-is-rot
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rota-1-rot-11-b11-01 (p p))
                 (:instance rota-1-rot-11-b11-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-11)
                                    (rota-1-rot-11-b11-01-1-witness p))))
                 (:instance b11-01 (p (rota-1-rot-11-b11-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-11))
                            (p (rota-1-rot-11-b11-01-1-witness p)))
                 (:instance b3-0-set-a11 (p (rota-1-rot-11-b11-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-11)
                                             (rota-1-rot-11-b11-01-1-witness p))))
                 (:instance rot-11-inv*f (point (rota-1-rot-11-b11-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-11))
                            (p1 (rot-11-inv*f-witness (rota-1-rot-11-b11-01-1-witness p)))
                            (p2 (rota-1-rot-11-b11-01-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance rota-1-rot-12-b12-11 (p p))
                 (:instance rota-1-rot-12-b12-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-12)
                                    (rota-1-rot-12-b12-11-1-witness p))))
                 (:instance b12-11 (p (rota-1-rot-12-b12-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-12))
                            (p (rota-1-rot-12-b12-11-1-witness p)))
                 (:instance b3-0-set-a12 (p (rota-1-rot-12-b12-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-12)
                                             (rota-1-rot-12-b12-11-1-witness p))))
                 (:instance rot-12-inv*f (point (rota-1-rot-12-b12-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-12))
                            (p1 (rot-12-inv*f-witness (rota-1-rot-12-b12-11-1-witness p)))
                            (p2 (rota-1-rot-12-b12-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-12)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rota-1-rot-12-b12-01 (p p))
                 (:instance rota-1-rot-12-b12-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-12)
                                    (rota-1-rot-12-b12-01-1-witness p))))
                 (:instance b12-01 (p (rota-1-rot-12-b12-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-12))
                            (p (rota-1-rot-12-b12-01-1-witness p)))
                 (:instance b3-0-set-a12 (p (rota-1-rot-12-b12-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-12)
                                             (rota-1-rot-12-b12-01-1-witness p))))
                 (:instance rot-12-inv*f (point (rota-1-rot-12-b12-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-12))
                            (p1 (rot-12-inv*f-witness (rota-1-rot-12-b12-01-1-witness p)))
                            (p2 (rota-1-rot-12-b12-01-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance rota-1-rot-13-b13-11 (p p))
                 (:instance rota-1-rot-13-b13-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-13)
                                    (rota-1-rot-13-b13-11-1-witness p))))
                 (:instance b13-11 (p (rota-1-rot-13-b13-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-13))
                            (p (rota-1-rot-13-b13-11-1-witness p)))
                 (:instance b3-0-set-a13 (p (rota-1-rot-13-b13-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-13)
                                             (rota-1-rot-13-b13-11-1-witness p))))
                 (:instance rot-13-inv*f (point (rota-1-rot-13-b13-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-13))
                            (p1 (rot-13-inv*f-witness (rota-1-rot-13-b13-11-1-witness p)))
                            (p2 (rota-1-rot-13-b13-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-13)
                 (:instance rota-1-rot-13-b13-01 (p p))
                 (:instance rota-1-rot-13-b13-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-13)
                                    (rota-1-rot-13-b13-01-1-witness p))))
                 (:instance b13-01 (p (rota-1-rot-13-b13-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-13))
                            (p (rota-1-rot-13-b13-01-1-witness p)))
                 (:instance b3-0-set-a13 (p (rota-1-rot-13-b13-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-13)
                                             (rota-1-rot-13-b13-01-1-witness p))))
                 (:instance rot-13-inv*f (point (rota-1-rot-13-b13-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-13))
                            (p1 (rot-13-inv*f-witness (rota-1-rot-13-b13-01-1-witness p)))
                            (p2 (rota-1-rot-13-b13-01-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rota-1-rot-14-b14-11 (p p))
                 (:instance rota-1-rot-14-b14-11-1 (point p))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-14)
                                    (rota-1-rot-14-b14-11-1-witness p))))
                 (:instance b14-11 (p (rota-1-rot-14-b14-11-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-14))
                            (p (rota-1-rot-14-b14-11-1-witness p)))
                 (:instance b3-0-set-a14 (p (rota-1-rot-14-b14-11-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-14)
                                             (rota-1-rot-14-b14-11-1-witness p))))
                 (:instance rot-14-inv*f (point (rota-1-rot-14-b14-11-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-14))
                            (p1 (rot-14-inv*f-witness (rota-1-rot-14-b14-11-1-witness p)))
                            (p2 (rota-1-rot-14-b14-11-1-witness p)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-14)
                 (:instance rota-1-rot-14-b14-01 (p p))
                 (:instance rota-1-rot-14-b14-01-1 (point p))
                 (:instance rota-inv-b3-0-n-f-1-suff
                            (point p)
                            (p (m-* (rot-14)
                                    (rota-1-rot-14-b14-01-1-witness p))))
                 (:instance b14-01 (p (rota-1-rot-14-b14-01-1-witness p)))
                 (:instance rot*b3-0-set=>b3-0
                            (rot (rot-14))
                            (p (rota-1-rot-14-b14-01-1-witness p)))
                 (:instance b3-0-set-a14 (p (rota-1-rot-14-b14-01-1-witness p)))
                 (:instance b3-0-n-f (p (m-* (rot-14)
                                             (rota-1-rot-14-b14-01-1-witness p))))
                 (:instance rot-14-inv*f (point (rota-1-rot-14-b14-01-1-witness p)))
                 (:instance rota-1-rot-3-b3-01-or-11=>2
                            (rot (rot-14))
                            (p1 (rot-14-inv*f-witness (rota-1-rot-14-b14-01-1-witness p)))
                            (p2 (rota-1-rot-14-b14-01-1-witness p)))
                 )
           :in-theory nil
           )
          ))

(defun-sk rot-9-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-9)) p) point))))

(defun b9-00 (p)
  (and (b3-0-set-a9 p)
       (b3-f p)
       (rot-9-inv*b3-f p)))

(defun b9-10 (p)
  (and (b3-0-set-a9 p)
       (set-f-p p)
       (rot-9-inv*b3-f p)))

(defun-sk rot-9-b9-00-1 (point)
  (exists p
          (and (b9-00 p)
               (m-= (m-* (rot-9) p) point))))

(defun rot-9-b9-00 (p)
  (and (point-in-r3 p)
       (rot-9-b9-00-1 p)))

(defun-sk rot-9-b9-10-1 (point)
  (exists p
          (and (b9-10 p)
               (m-= (m-* (rot-9) p) point))))

(defun rot-9-b9-10 (p)
  (and (point-in-r3 p)
       (rot-9-b9-10-1 p)))

(defun-sk rot-10-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-10)) p) point))))

(defun b10-00 (p)
  (and (b3-0-set-a10 p)
       (b3-f p)
       (rot-10-inv*b3-f p)))

(defun b10-10 (p)
  (and (b3-0-set-a10 p)
       (set-f-p p)
       (rot-10-inv*b3-f p)))

(defun-sk rot-10-b10-00-1 (point)
  (exists p
          (and (b10-00 p)
               (m-= (m-* (rot-10) p) point))))

(defun rot-10-b10-00 (p)
  (and (point-in-r3 p)
       (rot-10-b10-00-1 p)))

(defun-sk rot-10-b10-10-1 (point)
  (exists p
          (and (b10-10 p)
               (m-= (m-* (rot-10) p) point))))

(defun rot-10-b10-10 (p)
  (and (point-in-r3 p)
       (rot-10-b10-10-1 p)))

(defun-sk rot-11-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-11)) p) point))))

(defun b11-00 (p)
  (and (b3-0-set-a11 p)
       (b3-f p)
       (rot-11-inv*b3-f p)))

(defun b11-10 (p)
  (and (b3-0-set-a11 p)
       (set-f-p p)
       (rot-11-inv*b3-f p)))

(defun-sk rot-11-b11-00-1 (point)
  (exists p
          (and (b11-00 p)
               (m-= (m-* (rot-11) p) point))))

(defun rot-11-b11-00 (p)
  (and (point-in-r3 p)
       (rot-11-b11-00-1 p)))

(defun-sk rot-11-b11-10-1 (point)
  (exists p
          (and (b11-10 p)
               (m-= (m-* (rot-11) p) point))))

(defun rot-11-b11-10 (p)
  (and (point-in-r3 p)
       (rot-11-b11-10-1 p)))

(defun-sk rot-12-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-12)) p) point))))

(defun b12-00 (p)
  (and (b3-0-set-a12 p)
       (b3-f p)
       (rot-12-inv*b3-f p)))

(defun b12-10 (p)
  (and (b3-0-set-a12 p)
       (set-f-p p)
       (rot-12-inv*b3-f p)))

(defun-sk rot-12-b12-00-1 (point)
  (exists p
          (and (b12-00 p)
               (m-= (m-* (rot-12) p) point))))

(defun rot-12-b12-00 (p)
  (and (point-in-r3 p)
       (rot-12-b12-00-1 p)))

(defun-sk rot-12-b12-10-1 (point)
  (exists p
          (and (b12-10 p)
               (m-= (m-* (rot-12) p) point))))

(defun rot-12-b12-10 (p)
  (and (point-in-r3 p)
       (rot-12-b12-10-1 p)))

(defun-sk rot-13-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-13)) p) point))))

(defun b13-00 (p)
  (and (b3-0-set-a13 p)
       (b3-f p)
       (rot-13-inv*b3-f p)))

(defun b13-10 (p)
  (and (b3-0-set-a13 p)
       (set-f-p p)
       (rot-13-inv*b3-f p)))

(defun-sk rot-13-b13-00-1 (point)
  (exists p
          (and (b13-00 p)
               (m-= (m-* (rot-13) p) point))))

(defun rot-13-b13-00 (p)
  (and (point-in-r3 p)
       (rot-13-b13-00-1 p)))

(defun-sk rot-13-b13-10-1 (point)
  (exists p
          (and (b13-10 p)
               (m-= (m-* (rot-13) p) point))))

(defun rot-13-b13-10 (p)
  (and (point-in-r3 p)
       (rot-13-b13-10-1 p)))

(defun-sk rot-14-inv*b3-f (point)
  (exists p
          (and (b3-f p)
               (m-= (m-* (r3-m-inverse (rot-14)) p) point))))

(defun b14-00 (p)
  (and (b3-0-set-a14 p)
       (b3-f p)
       (rot-14-inv*b3-f p)))

(defun b14-10 (p)
  (and (b3-0-set-a14 p)
       (set-f-p p)
       (rot-14-inv*b3-f p)))

(defun-sk rot-14-b14-00-1 (point)
  (exists p
          (and (b14-00 p)
               (m-= (m-* (rot-14) p) point))))

(defun rot-14-b14-00 (p)
  (and (point-in-r3 p)
       (rot-14-b14-00-1 p)))

(defun-sk rot-14-b14-10-1 (point)
  (exists p
          (and (b14-10 p)
               (m-= (m-* (rot-14) p) point))))

(defun rot-14-b14-10 (p)
  (and (point-in-r3 p)
       (rot-14-b14-10-1 p)))

(defthmd a9-a14-b3-0-n-b3-f=>
  (implies (b3-0-n-b3-f p)
           (or (rot-9-b9-00 p)
               (rot-9-b9-10 p)
               (rot-10-b10-00 p)
               (rot-10-b10-10 p)
               (rot-11-b11-00 p)
               (rot-11-b11-10 p)
               (rot-12-b12-00 p)
               (rot-12-b12-10 p)
               (rot-13-b13-00 p)
               (rot-13-b13-10 p)
               (rot-14-b14-00 p)
               (rot-14-b14-10 p)))
  :hints (("goal"
           :cases ((b3-0-b-inv-b3-0-set-a9 p)
                   (b3-0-b-inv-r-b3-0-set-a10 p)
                   (b3-0-r-1-b-inv-b3-0-set-a11 p)
                   (b3-0-r-1-b-inv-r-b3-0-set-a12 p)
                   (b3-0-set-a13 p)
                   (b3-0-set-a14 p))
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b3-0-iff-a9-to-a14 (p p))
                 )
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance b3-0-b-inv-b3-0-set-a9 (p p))
                 (:instance b3-0-b-inv-b3-0-set-a9-1 (p p))
                 (:instance rot-9-b9-10 (p p))
                 (:instance rot-9-b9-10-1-suff (point p) (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance b9-10 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance b3-f (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance rot-9-b9-00 (p p))
                 (:instance rot-9-b9-00-1-suff (point p) (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance b9-00 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance rot-9)
                 (:instance rot-9-inv*b3-f-suff (p p) (point (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-9))
                            (m2 (b3-0-b-inv-b3-0-set-a9-1-witness p))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-9)))
                            (m5 (id-rotation))
                            (m6 (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance m-*point-id=point (p1 (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance b3-0-set-a9 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance m-*-m-inverse-m
                            (m (rot-9)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (b-inv-rotation (acl2-sqrt 2))))
                 (:instance b3 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance b3-0-b-inv-r-b3-0-set-a10 (p p))
                 (:instance b3-0-b-inv-r-b3-0-set-a10-1 (p p))
                 (:instance rot-10-b10-10 (p p))
                 (:instance rot-10-b10-10-1-suff (point p) (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance b10-10 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance b3-f (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance rot-10-b10-00 (p p))
                 (:instance rot-10-b10-00-1-suff (point p) (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance b10-00 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance rot-10)
                 (:instance rot-10-inv*b3-f-suff (p p) (point (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-10))
                            (m2 (b3-0-b-inv-r-b3-0-set-a10-1-witness p))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-10)))
                            (m5 (id-rotation))
                            (m6 (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance associativity-of-m-*
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (m3 (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance m-*point-id=point (p1 (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance b3-0-set-a10 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance m-*-m-inverse-m
                            (m (rot-10)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance rot*rot-is-rot
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance r3-rotationp (m (rot-10)))
                 (:instance b3 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance b3-0-r-1-b-inv-b3-0-set-a11 (p p))
                 (:instance b3-0-r-1-b-inv-b3-0-set-a11-1 (p p))
                 (:instance rot-11-b11-10 (p p))
                 (:instance rot-11-b11-10-1-suff (point p) (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance b11-10 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance b3-f (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance rot-11-b11-00 (p p))
                 (:instance rot-11-b11-00-1-suff (point p) (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance b11-00 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance rot-11)
                 (:instance rot-11-inv*b3-f-suff (p p) (point (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-11))
                            (m2 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-11)))
                            (m5 (id-rotation))
                            (m6 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance associativity-of-m-*
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance m-*point-id=point (p1 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance b3-0-set-a11 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance m-*-m-inverse-m
                            (m (rot-11)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance rot*rot-is-rot
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance r3-rotationp (m (rot-11)))
                 (:instance b3 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance b3-0-r-1-b-inv-r-b3-0-set-a12 (p p))
                 (:instance b3-0-r-1-b-inv-r-b3-0-set-a12-1 (p p))
                 (:instance rot-12-b12-10 (p p))
                 (:instance rot-12-b12-10-1-suff (point p) (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance b12-10 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance b3-f (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance rot-12-b12-00 (p p))
                 (:instance rot-12-b12-00-1-suff (point p) (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance b12-00 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance rot-12)
                 (:instance rot-12-inv*b3-f-suff (p p) (point (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-12))
                            (m2 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))
                            (m3 p)
                            (m4 (r3-m-inverse (rot-12)))
                            (m5 (id-rotation))
                            (m6 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>sub-3
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (m4 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance m-*point-id=point (p1 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance b3-0-set-a12 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance m-*-m-inverse-m
                            (m (rot-12)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance r3-rotationp (m (rot-12)))
                 (:instance b3 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance rot-13-b13-10 (p p))
                 (:instance rot-13-b13-10-1-suff (point p) (p p))
                 (:instance b13-10 (p p))
                 (:instance b3-f (p p))
                 (:instance b3-0-set-a13 (p p))
                 (:instance rot-13-b13-00 (p p))
                 (:instance rot-13-b13-00-1-suff (point p) (p p))
                 (:instance b13-00 (p p))
                 (:instance rot-13)
                 (:instance rot-13-inv*b3-f-suff (p p) (point p))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-13))
                            (m2 p)
                            (m3 p)
                            (m4 (r3-m-inverse (rot-13)))
                            (m5 (id-rotation))
                            (m6 p))
                 (:instance m-*point-id=point (p1 p))
                 (:instance m-*-m-inverse-m
                            (m (rot-13)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (id-rotation)))
                 )
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rot-14-b14-10 (p p))
                 (:instance rot-14-b14-10-1-suff (point p) (p p))
                 (:instance b14-10 (p p))
                 (:instance b3-f (p p))
                 (:instance b3-0-set-a14 (p p))
                 (:instance rot-14-b14-00 (p p))
                 (:instance rot-14-b14-00-1-suff (point p) (p p))
                 (:instance b14-00 (p p))
                 (:instance rot-14)
                 (:instance rot-14-inv*b3-f-suff (p p) (point p))
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>1
                            (m1 (rot-14))
                            (m2 p)
                            (m3 p)
                            (m4 (r3-m-inverse (rot-14)))
                            (m5 (id-rotation))
                            (m6 p))
                 (:instance m-*point-id=point (p1 p))
                 (:instance m-*-m-inverse-m
                            (m (rot-14)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (id-rotation)))
                 )
           :in-theory nil
           )
          ))

(defthmd rot-9-14-b-9-14-01-or-11=>
  (implies (or (rot-9-b9-00 p)
               (rot-9-b9-10 p)
               (rot-10-b10-00 p)
               (rot-10-b10-10 p)
               (rot-11-b11-00 p)
               (rot-11-b11-10 p)
               (rot-12-b12-00 p)
               (rot-12-b12-10 p)
               (rot-13-b13-00 p)
               (rot-13-b13-10 p)
               (rot-14-b14-00 p)
               (rot-14-b14-10 p))
           (b3-0-n-b3-f p))
  :hints (("goal"
           :cases ((rot-9-b9-00 p)
                   (rot-9-b9-10 p)
                   (rot-10-b10-00 p)
                   (rot-10-b10-10 p)
                   (rot-11-b11-00 p)
                   (rot-11-b11-10 p)
                   (rot-12-b12-00 p)
                   (rot-12-b12-10 p)
                   (rot-13-b13-00 p)
                   (rot-13-b13-10 p)
                   (rot-14-b14-00 p)
                   (rot-14-b14-10 p))
           :in-theory nil
           )
          ("subgoal 12"
           :use ((:instance rot-9-b9-00 (p p))
                 (:instance rot-9-b9-00-1 (point p))
                 (:instance b9-00 (p (rot-9-b9-00-1-witness p)))
                 (:instance rot-9-inv*b3-f (point (rot-9-b9-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-9-b9-00-1-witness p))
                            (rot (rot-9)))
                 (:instance rot-9)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-9) (rot-9-b9-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-9) (rot-9-b9-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-9))
                            (wit (rot-9-b9-00-1-witness p))
                            (p p)
                            (wit-wit (rot-9-inv*b3-f-witness (rot-9-b9-00-1-witness p))))
                 (:instance b3 (p (rot-9-inv*b3-f-witness (rot-9-b9-00-1-witness p))))
                 (:instance b3-f (p (rot-9-inv*b3-f-witness (rot-9-b9-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 11"
           :use ((:instance rot-9-b9-10 (p p))
                 (:instance rot-9-b9-10-1 (point p))
                 (:instance b9-10 (p (rot-9-b9-10-1-witness p)))
                 (:instance rot-9-inv*b3-f (point (rot-9-b9-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-9-b9-10-1-witness p))
                            (rot (rot-9)))
                 (:instance rot-9)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-9) (rot-9-b9-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-9) (rot-9-b9-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-9))
                            (wit (rot-9-b9-10-1-witness p))
                            (p p)
                            (wit-wit (rot-9-inv*b3-f-witness (rot-9-b9-10-1-witness p))))
                 (:instance b3 (p (rot-9-inv*b3-f-witness (rot-9-b9-10-1-witness p))))
                 (:instance b3-f (p (rot-9-inv*b3-f-witness (rot-9-b9-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 10"
           :use ((:instance rot-10-b10-00 (p p))
                 (:instance rot-10-b10-00-1 (point p))
                 (:instance b10-00 (p (rot-10-b10-00-1-witness p)))
                 (:instance rot-10-inv*b3-f (point (rot-10-b10-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-10-b10-00-1-witness p))
                            (rot (rot-10)))
                 (:instance rot-10)
                 (:instance rot*rot-is-rot
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-10) (rot-10-b10-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-10) (rot-10-b10-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-10))
                            (wit (rot-10-b10-00-1-witness p))
                            (p p)
                            (wit-wit (rot-10-inv*b3-f-witness (rot-10-b10-00-1-witness p))))
                 (:instance b3 (p (rot-10-inv*b3-f-witness (rot-10-b10-00-1-witness p))))
                 (:instance b3-f (p (rot-10-inv*b3-f-witness (rot-10-b10-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 9"
           :use ((:instance rot-10-b10-10 (p p))
                 (:instance rot-10-b10-10-1 (point p))
                 (:instance b10-10 (p (rot-10-b10-10-1-witness p)))
                 (:instance rot-10-inv*b3-f (point (rot-10-b10-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-10-b10-10-1-witness p))
                            (rot (rot-10)))
                 (:instance rot-10)
                 (:instance rot*rot-is-rot
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-10) (rot-10-b10-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-10) (rot-10-b10-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-10))
                            (wit (rot-10-b10-10-1-witness p))
                            (p p)
                            (wit-wit (rot-10-inv*b3-f-witness (rot-10-b10-10-1-witness p))))
                 (:instance b3 (p (rot-10-inv*b3-f-witness (rot-10-b10-10-1-witness p))))
                 (:instance b3-f (p (rot-10-inv*b3-f-witness (rot-10-b10-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 8"
           :use ((:instance rot-11-b11-00 (p p))
                 (:instance rot-11-b11-00-1 (point p))
                 (:instance b11-00 (p (rot-11-b11-00-1-witness p)))
                 (:instance rot-11-inv*b3-f (point (rot-11-b11-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-11-b11-00-1-witness p))
                            (rot (rot-11)))
                 (:instance rot-11)
                 (:instance rot*rot-is-rot
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-11) (rot-11-b11-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-11) (rot-11-b11-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-11))
                            (wit (rot-11-b11-00-1-witness p))
                            (p p)
                            (wit-wit (rot-11-inv*b3-f-witness (rot-11-b11-00-1-witness p))))
                 (:instance b3 (p (rot-11-inv*b3-f-witness (rot-11-b11-00-1-witness p))))
                 (:instance b3-f (p (rot-11-inv*b3-f-witness (rot-11-b11-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 7"
           :use ((:instance rot-11-b11-10 (p p))
                 (:instance rot-11-b11-10-1 (point p))
                 (:instance b11-10 (p (rot-11-b11-10-1-witness p)))
                 (:instance rot-11-inv*b3-f (point (rot-11-b11-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-11-b11-10-1-witness p))
                            (rot (rot-11)))
                 (:instance rot-11)
                 (:instance rot*rot-is-rot
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-11) (rot-11-b11-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-11) (rot-11-b11-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-11))
                            (wit (rot-11-b11-10-1-witness p))
                            (p p)
                            (wit-wit (rot-11-inv*b3-f-witness (rot-11-b11-10-1-witness p))))
                 (:instance b3 (p (rot-11-inv*b3-f-witness (rot-11-b11-10-1-witness p))))
                 (:instance b3-f (p (rot-11-inv*b3-f-witness (rot-11-b11-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance rot-12-b12-00 (p p))
                 (:instance rot-12-b12-00-1 (point p))
                 (:instance b12-00 (p (rot-12-b12-00-1-witness p)))
                 (:instance rot-12-inv*b3-f (point (rot-12-b12-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-12-b12-00-1-witness p))
                            (rot (rot-12)))
                 (:instance rot-12)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-12) (rot-12-b12-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-12) (rot-12-b12-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-12))
                            (wit (rot-12-b12-00-1-witness p))
                            (p p)
                            (wit-wit (rot-12-inv*b3-f-witness (rot-12-b12-00-1-witness p))))
                 (:instance b3 (p (rot-12-inv*b3-f-witness (rot-12-b12-00-1-witness p))))
                 (:instance b3-f (p (rot-12-inv*b3-f-witness (rot-12-b12-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance rot-12-b12-10 (p p))
                 (:instance rot-12-b12-10-1 (point p))
                 (:instance b12-10 (p (rot-12-b12-10-1-witness p)))
                 (:instance rot-12-inv*b3-f (point (rot-12-b12-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-12-b12-10-1-witness p))
                            (rot (rot-12)))
                 (:instance rot-12)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d
                                 (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0 (p (m-* (rot-12) (rot-12-b12-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-12) (rot-12-b12-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-12))
                            (wit (rot-12-b12-10-1-witness p))
                            (p p)
                            (wit-wit (rot-12-inv*b3-f-witness (rot-12-b12-10-1-witness p))))
                 (:instance b3 (p (rot-12-inv*b3-f-witness (rot-12-b12-10-1-witness p))))
                 (:instance b3-f (p (rot-12-inv*b3-f-witness (rot-12-b12-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance rot-13-b13-00 (p p))
                 (:instance rot-13-b13-00-1 (point p))
                 (:instance b13-00 (p (rot-13-b13-00-1-witness p)))
                 (:instance rot-13-inv*b3-f (point (rot-13-b13-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-13-b13-00-1-witness p))
                            (rot (rot-13)))
                 (:instance rot-13)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-13) (rot-13-b13-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-13) (rot-13-b13-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-13))
                            (wit (rot-13-b13-00-1-witness p))
                            (p p)
                            (wit-wit (rot-13-inv*b3-f-witness (rot-13-b13-00-1-witness p))))
                 (:instance b3 (p (rot-13-inv*b3-f-witness (rot-13-b13-00-1-witness p))))
                 (:instance b3-f (p (rot-13-inv*b3-f-witness (rot-13-b13-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance rot-13-b13-10 (p p))
                 (:instance rot-13-b13-10-1 (point p))
                 (:instance b13-10 (p (rot-13-b13-10-1-witness p)))
                 (:instance rot-13-inv*b3-f (point (rot-13-b13-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-13-b13-10-1-witness p))
                            (rot (rot-13)))
                 (:instance rot-13)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-13) (rot-13-b13-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-13) (rot-13-b13-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-13))
                            (wit (rot-13-b13-10-1-witness p))
                            (p p)
                            (wit-wit (rot-13-inv*b3-f-witness (rot-13-b13-10-1-witness p))))
                 (:instance b3 (p (rot-13-inv*b3-f-witness (rot-13-b13-10-1-witness p))))
                 (:instance b3-f (p (rot-13-inv*b3-f-witness (rot-13-b13-10-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance rot-14-b14-00 (p p))
                 (:instance rot-14-b14-00-1 (point p))
                 (:instance b14-00 (p (rot-14-b14-00-1-witness p)))
                 (:instance rot-14-inv*b3-f (point (rot-14-b14-00-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-14-b14-00-1-witness p))
                            (rot (rot-14)))
                 (:instance rot-14)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-14) (rot-14-b14-00-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-14) (rot-14-b14-00-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-14))
                            (wit (rot-14-b14-00-1-witness p))
                            (p p)
                            (wit-wit (rot-14-inv*b3-f-witness (rot-14-b14-00-1-witness p))))
                 (:instance b3 (p (rot-14-inv*b3-f-witness (rot-14-b14-00-1-witness p))))
                 (:instance b3-f (p (rot-14-inv*b3-f-witness (rot-14-b14-00-1-witness p))))
                 )
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rot-14-b14-10 (p p))
                 (:instance rot-14-b14-10-1 (point p))
                 (:instance b14-10 (p (rot-14-b14-10-1-witness p)))
                 (:instance rot-14-inv*b3-f (point (rot-14-b14-10-1-witness p)))
                 (:instance b3-0-n-b3-f (p p))
                 (:instance rot*b3-0-set=>b3-0
                            (p (rot-14-b14-10-1-witness p))
                            (rot (rot-14)))
                 (:instance rot-14)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0 (p (m-* (rot-14) (rot-14-b14-10-1-witness p))))
                 (:instance b3-0 (p p))
                 (:instance cal-radius-p1=p2
                            (p1 (m-* (rot-14) (rot-14-b14-10-1-witness p)))
                            (p2 p))
                 (:instance b3-f (p p))
                 (:instance b3 (p p))
                 (:instance rot-3-8-b-3-8-01-or-11=>1
                            (rot (rot-14))
                            (wit (rot-14-b14-10-1-witness p))
                            (p p)
                            (wit-wit (rot-14-inv*b3-f-witness (rot-14-b14-10-1-witness p))))
                 (:instance b3 (p (rot-14-inv*b3-f-witness (rot-14-b14-10-1-witness p))))
                 (:instance b3-f (p (rot-14-inv*b3-f-witness (rot-14-b14-10-1-witness p))))
                 )
           :in-theory nil
           )
          ))

(defun set-b10 (p)
  (and (b3-0-set-a1 p)
       (b3-f p)))

(defun set-b20 (p)
  (and (b3-0-set-a2 p)
       (b3-f p)))

(defthmd b3-0-n-b3-f=>1-14
  (implies (b3-0-n-b3-f p)
           (or (b3-00 p)
               (b3-01 p)
               (b4-00 p)
               (b4-01 p)
               (b5-00 p)
               (b5-01 p)
               (b6-00 p)
               (b6-01 p)
               (b7-00 p)
               (b7-01 p)
               (b8-00 p)
               (b8-01 p)
               (b9-00 p)
               (b9-01 p)
               (b10-00 p)
               (b10-01 p)
               (b11-00 p)
               (b11-01 p)
               (b12-00 p)
               (b12-01 p)
               (b13-00 p)
               (b13-01 p)
               (b14-00 p)
               (b14-01 p)
               (set-b20 p)
               (set-b10 p)))
  :hints (("goal"
           :cases ((b3-0-set-a3 p)
                   (b3-0-set-a4 p)
                   (b3-0-set-a5 p)
                   (b3-0-set-a6 p)
                   (b3-0-set-a7 p)
                   (b3-0-set-a8 p)
                   (b3-0-set-a9 p)
                   (b3-0-set-a10 p)
                   (b3-0-set-a11 p)
                   (b3-0-set-a12 p)
                   (b3-0-set-a13 p)
                   (b3-0-set-a14 p)
                   (b3-0-set-a2 p)
                   (b3-0-set-a1 p))
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b3-0-iff-a1-to-a14 (p p))
                 )
           :in-theory nil
           )
          ("subgoal 14"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b3-00 (p p))
                 (:instance b3-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-3)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-3)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-3)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-3))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-3))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-3))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-3))) (point p))
                 (:instance rot-3-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-3))
                                                                               p)))
                 (:instance rot-3-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-3))
                                                                                 p)))
                 )
           :in-theory nil
           )
          ("subgoal 13"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b4-00 (p p))
                 (:instance b4-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-4)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-4)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-4)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-4))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-4))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-4))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-4))) (point p))
                 (:instance rot-4-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-4))
                                                                               p)))
                 (:instance rot-4-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-4))
                                                                                 p)))
                 )
           :in-theory nil
           )
          ("subgoal 12"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b5-00 (p p))
                 (:instance b5-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-5)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-5)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-5)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d))))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-5))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-5))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-5))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-5))) (point p))
                 (:instance rot-5-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-5))
                                                                               p)))
                 (:instance rot-5-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-5))
                                                                                 p)))
                 )
           :in-theory nil
           )
          ("subgoal 11"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b6-00 (p p))
                 (:instance b6-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-6)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-6)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-6)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-6))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-6))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-6))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-6))) (point p))
                 (:instance rot-6-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-6))
                                                                               p)))
                 (:instance rot-6-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-6))
                                                                                 p)))
                 )
           :in-theory nil
           )
          ("subgoal 10"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b7-00 (p p))
                 (:instance b7-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-7)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-7)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-7)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-7))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-7))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-7))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-7))) (point p))
                 (:instance rot-7-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-7))
                                                                               p)))
                 (:instance rot-7-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-7))
                                                                                 p)))
                 )
           :in-theory nil
           )
          ("subgoal 9"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b8-00 (p p))
                 (:instance b8-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-8)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-8)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-8)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-8))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-8))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-8))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-8))) (point p))
                 (:instance rot-8-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-8))
                                                                               p)))
                 (:instance rot-8-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-8))
                                                                                 p)))
                 )
           :in-theory nil
           )

          ("subgoal 8"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b9-00 (p p))
                 (:instance b9-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-9)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-9)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-9)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-9))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-9))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-9))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-9))) (point p))
                 (:instance rot-9-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-9))
                                                                               p)))
                 (:instance rot-9-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-9))
                                                                                 p)))
                 )
           :in-theory nil
           )
          ("subgoal 7"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b10-00 (p p))
                 (:instance b10-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-10)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-10)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-10)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*rot-is-rot
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-10))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-10))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-10))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-10))) (point p))
                 (:instance rot-10-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-10))
                                                                                p)))
                 (:instance rot-10-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-10))
                                                                                  p)))
                 )
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b11-00 (p p))
                 (:instance b11-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-11)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-11)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-11)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*rot-is-rot
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d))))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-11))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-11))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-11))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-11))) (point p))
                 (:instance rot-11-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-11))
                                                                                p)))
                 (:instance rot-11-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-11))
                                                                                  p)))
                 )
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b12-00 (p p))
                 (:instance b12-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-12)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-12)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-12)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-12))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-12))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-12))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-12))) (point p))
                 (:instance rot-12-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-12))
                                                                                p)))
                 (:instance rot-12-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-12))
                                                                                  p)))
                 )
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b13-00 (p p))
                 (:instance b13-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-13)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-13)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-13)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-13))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-13))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-13))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-13))) (point p))
                 (:instance rot-13-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-13))
                                                                                p)))
                 (:instance rot-13-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-13))
                                                                                  p)))
                 )
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b14-00 (p p))
                 (:instance b14-01 (p p))
                 (:instance b3-f (p p))
                 (:instance rot-14)
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (rot (r3-m-inverse (rot-14)))
                            (p p))
                 (:instance rot-m=>rot-m-inv
                            (m (rot-14)))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-14))) (p p))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-14))) (point p))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-14))) (p p))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-14))) (point p))
                 (:instance rot-14-inv*f-suff (point p) (p (rot*set-f-1-witness (r3-m-inverse (rot-14))
                                                                                p)))
                 (:instance rot-14-inv*b3-f-suff (point p) (p (rot*b3-f-1-witness (r3-m-inverse (rot-14))
                                                                                  p)))
                 )
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance set-b20 (p p))
                 )
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance set-b10 (p p))
                 )
           :in-theory nil
           )
          ))

(defthmd 1-14=>b3-0-n-b3-f
  (implies (or (b3-00 p)
               (b3-01 p)
               (b4-00 p)
               (b4-01 p)
               (b5-00 p)
               (b5-01 p)
               (b6-00 p)
               (b6-01 p)
               (b7-00 p)
               (b7-01 p)
               (b8-00 p)
               (b8-01 p)
               (b9-00 p)
               (b9-01 p)
               (b10-00 p)
               (b10-01 p)
               (b11-00 p)
               (b11-01 p)
               (b12-00 p)
               (b12-01 p)
               (b13-00 p)
               (b13-01 p)
               (b14-00 p)
               (b14-01 p)
               (set-b20 p)
               (set-b10 p))
           (b3-0-n-b3-f p))
  :hints (("goal"
           :use ((:instance b3-0-n-b3-f (p p))
                 (:instance b3-0-iff-a1-to-a14 (p p))
                 (:instance b3-00 (p p))
                 (:instance b3-01 (p p))
                 (:instance b4-00 (p p))
                 (:instance b4-01 (p p))
                 (:instance b5-00 (p p))
                 (:instance b5-01 (p p))
                 (:instance b6-00 (p p))
                 (:instance b6-01 (p p))
                 (:instance b7-00 (p p))
                 (:instance b7-01 (p p))
                 (:instance b8-00 (p p))
                 (:instance b8-01 (p p))
                 (:instance b9-00 (p p))
                 (:instance b9-01 (p p))
                 (:instance b10-00 (p p))
                 (:instance b10-01 (p p))
                 (:instance b11-00 (p p))
                 (:instance b11-01 (p p))
                 (:instance b12-00 (p p))
                 (:instance b12-01 (p p))
                 (:instance b13-00 (p p))
                 (:instance b13-01 (p p))
                 (:instance b14-00 (p p))
                 (:instance b14-01 (p p))
                 (:instance set-b20 (p p))
                 (:instance set-b10 (p p)))
           :in-theory nil
           )))

(defun set-b11 (p)
  (and (b3-0-set-a1 p)
       (set-f-p p)))

(defun set-b21 (p)
  (and (b3-0-set-a2 p)
       (set-f-p p)))

(defun-sk rota-1-b11-1 (point)
  (exists p
          (and (set-b11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b11 (p)
  (and (point-in-r3 p)
       (rota-1-b11-1 p)))

(defun-sk rota-1-b21-1 (point)
  (exists p
          (and (set-b21 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b21 (p)
  (and (point-in-r3 p)
       (rota-1-b21-1 p)))

(defun-sk rota-1-b3-10-1 (point)
  (exists p
          (and (b3-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b3-10 (p)
  (and (point-in-r3 p)
       (rota-1-b3-10-1 p)))

(defun-sk rota-1-b3-11-1 (point)
  (exists p
          (and (b3-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b3-11 (p)
  (and (point-in-r3 p)
       (rota-1-b3-11-1 p)))

(defun-sk rota-1-b4-10-1 (point)
  (exists p
          (and (b4-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b4-10 (p)
  (and (point-in-r3 p)
       (rota-1-b4-10-1 p)))

(defun-sk rota-1-b4-11-1 (point)
  (exists p
          (and (b4-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b4-11 (p)
  (and (point-in-r3 p)
       (rota-1-b4-11-1 p)))

(defun-sk rota-1-b5-10-1 (point)
  (exists p
          (and (b5-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b5-10 (p)
  (and (point-in-r3 p)
       (rota-1-b5-10-1 p)))

(defun-sk rota-1-b5-11-1 (point)
  (exists p
          (and (b5-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b5-11 (p)
  (and (point-in-r3 p)
       (rota-1-b5-11-1 p)))

(defun-sk rota-1-b6-10-1 (point)
  (exists p
          (and (b6-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b6-10 (p)
  (and (point-in-r3 p)
       (rota-1-b6-10-1 p)))

(defun-sk rota-1-b6-11-1 (point)
  (exists p
          (and (b6-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b6-11 (p)
  (and (point-in-r3 p)
       (rota-1-b6-11-1 p)))

(defun-sk rota-1-b7-10-1 (point)
  (exists p
          (and (b7-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b7-10 (p)
  (and (point-in-r3 p)
       (rota-1-b7-10-1 p)))

(defun-sk rota-1-b7-11-1 (point)
  (exists p
          (and (b7-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b7-11 (p)
  (and (point-in-r3 p)
       (rota-1-b7-11-1 p)))

(defun-sk rota-1-b8-10-1 (point)
  (exists p
          (and (b8-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b8-10 (p)
  (and (point-in-r3 p)
       (rota-1-b8-10-1 p)))

(defun-sk rota-1-b8-11-1 (point)
  (exists p
          (and (b8-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b8-11 (p)
  (and (point-in-r3 p)
       (rota-1-b8-11-1 p)))

(defun-sk rota-1-b9-10-1 (point)
  (exists p
          (and (b9-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b9-10 (p)
  (and (point-in-r3 p)
       (rota-1-b9-10-1 p)))

(defun-sk rota-1-b9-11-1 (point)
  (exists p
          (and (b9-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b9-11 (p)
  (and (point-in-r3 p)
       (rota-1-b9-11-1 p)))

(defun-sk rota-1-b10-10-1 (point)
  (exists p
          (and (b10-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b10-10 (p)
  (and (point-in-r3 p)
       (rota-1-b10-10-1 p)))

(defun-sk rota-1-b10-11-1 (point)
  (exists p
          (and (b10-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b10-11 (p)
  (and (point-in-r3 p)
       (rota-1-b10-11-1 p)))

(defun-sk rota-1-b11-10-1 (point)
  (exists p
          (and (b11-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b11-10 (p)
  (and (point-in-r3 p)
       (rota-1-b11-10-1 p)))

(defun-sk rota-1-b11-11-1 (point)
  (exists p
          (and (b11-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b11-11 (p)
  (and (point-in-r3 p)
       (rota-1-b11-11-1 p)))

(defun-sk rota-1-b12-10-1 (point)
  (exists p
          (and (b12-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b12-10 (p)
  (and (point-in-r3 p)
       (rota-1-b12-10-1 p)))

(defun-sk rota-1-b12-11-1 (point)
  (exists p
          (and (b12-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b12-11 (p)
  (and (point-in-r3 p)
       (rota-1-b12-11-1 p)))

(defun-sk rota-1-b13-10-1 (point)
  (exists p
          (and (b13-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b13-10 (p)
  (and (point-in-r3 p)
       (rota-1-b13-10-1 p)))

(defun-sk rota-1-b13-11-1 (point)
  (exists p
          (and (b13-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b13-11 (p)
  (and (point-in-r3 p)
       (rota-1-b13-11-1 p)))

(defun-sk rota-1-b14-10-1 (point)
  (exists p
          (and (b14-10 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b14-10 (p)
  (and (point-in-r3 p)
       (rota-1-b14-10-1 p)))

(defun-sk rota-1-b14-11-1 (point)
  (exists p
          (and (b14-11 p)
               (m-= (rotation-about-arbitrary-line (- (angle-const)) (m-p) (n-p) p) point))))

(defun rota-1-b14-11 (p)
  (and (point-in-r3 p)
       (rota-1-b14-11-1 p)))

(defthmd rota-inv-b3-0-n-f=>rota-inv-1-14
  (implies (rota-inv-b3-0-n-f p)
           (or (rota-1-b3-10 p)
               (rota-1-b3-11 p)
               (rota-1-b4-10 p)
               (rota-1-b4-11 p)
               (rota-1-b5-10 p)
               (rota-1-b5-11 p)
               (rota-1-b6-10 p)
               (rota-1-b6-11 p)
               (rota-1-b7-10 p)
               (rota-1-b7-11 p)
               (rota-1-b8-10 p)
               (rota-1-b8-11 p)
               (rota-1-b9-10 p)
               (rota-1-b9-11 p)
               (rota-1-b10-10 p)
               (rota-1-b10-11 p)
               (rota-1-b11-10 p)
               (rota-1-b11-11 p)
               (rota-1-b12-10 p)
               (rota-1-b12-11 p)
               (rota-1-b13-10 p)
               (rota-1-b13-11 p)
               (rota-1-b14-10 p)
               (rota-1-b14-11 p)
               (rota-1-b21 p)
               (rota-1-b11 p)
               ))
  :hints (("goal"
           :cases ((b3-0-set-a3 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a4 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a5 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a6 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a7 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a8 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a9 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a10 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a11 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a12 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a13 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a14 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a2 (rota-inv-b3-0-n-f-1-witness p))
                   (b3-0-set-a1 (rota-inv-b3-0-n-f-1-witness p)))
           :use ((:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1 (point p))
                 (:instance b3-0-n-f (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-inv-b3-0-n-f-1-witness p))))
           :in-theory nil
           )

          ("subgoal 14"
           :use ((:instance rota-1-b3-10 (p p))
                 (:instance rota-1-b3-11 (p p))
                 (:instance rota-1-b3-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b3-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-3))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-3))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-3))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-3))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-3))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-3-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-3))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-3-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-3))
                                                    (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-3)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-3)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 13"
           :use ((:instance rota-1-b4-10 (p p))
                 (:instance rota-1-b4-11 (p p))
                 (:instance rota-1-b4-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b4-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b4-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b4-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-4))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-4))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-4))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-4))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-4))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-4-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-4))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-4-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-4))
                                                    (rota-inv-b3-0-n-f-1-witness
                                                     p))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*rot-is-rot (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-4)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-4)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 12"
           :use ((:instance rota-1-b5-10 (p p))
                 (:instance rota-1-b5-11 (p p))
                 (:instance rota-1-b5-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b5-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b5-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b5-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-5))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-5))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-5))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-5))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-5))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-5-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-5))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-5-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-5))
                                                    (rota-inv-b3-0-n-f-1-witness
                                                     p))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*rot-is-rot (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-5)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-5)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 11"
           :use ((:instance rota-1-b6-10 (p p))
                 (:instance rota-1-b6-11 (p p))
                 (:instance rota-1-b6-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b6-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b6-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b6-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-6))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-6))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-6))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-6))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-6))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-6-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-6))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-6-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-6))
                                                    (rota-inv-b3-0-n-f-1-witness
                                                     p))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-6)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-6)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 10"
           :use ((:instance rota-1-b7-10 (p p))
                 (:instance rota-1-b7-11 (p p))
                 (:instance rota-1-b7-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b7-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b7-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b7-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-7))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-7))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-7))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-7))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-7))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-7-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-7))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-7-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-7))
                                                    (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-7)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-7)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 9"
           :use ((:instance rota-1-b8-10 (p p))
                 (:instance rota-1-b8-11 (p p))
                 (:instance rota-1-b8-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b8-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b8-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b8-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-8))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-8))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-8))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-8))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-8))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-8-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-8))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-8-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-8))
                                                    (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-8)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-8)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )

          ("subgoal 8"
           :use ((:instance rota-1-b9-10 (p p))
                 (:instance rota-1-b9-11 (p p))
                 (:instance rota-1-b9-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b9-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b9-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b9-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-9))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-9))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-9))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-9))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-9))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-9-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-9))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-9-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-9))
                                                    (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-9)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-9)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 7"
           :use ((:instance rota-1-b10-10 (p p))
                 (:instance rota-1-b10-11 (p p))
                 (:instance rota-1-b10-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b10-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b10-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b10-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-10))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-10))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-10))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-10))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-10))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-10-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-10))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-10-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-10))
                                                    (rota-inv-b3-0-n-f-1-witness
                                                     p))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*rot-is-rot (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-10)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-10)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 6"
           :use ((:instance rota-1-b11-10 (p p))
                 (:instance rota-1-b11-11 (p p))
                 (:instance rota-1-b11-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b11-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b11-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b11-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-11))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-11))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-11))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-11))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-11))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-11-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-11))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-11-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-11))
                                                    (rota-inv-b3-0-n-f-1-witness
                                                     p))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*rot-is-rot (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-11)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-11)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance rota-1-b12-10 (p p))
                 (:instance rota-1-b12-11 (p p))
                 (:instance rota-1-b12-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b12-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b12-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b12-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-12))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-12))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-12))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-12))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-12))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-12-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-12))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-12-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-12))
                                                    (rota-inv-b3-0-n-f-1-witness
                                                     p))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-12)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-12)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 4"
           :use ((:instance rota-1-b13-10 (p p))
                 (:instance rota-1-b13-11 (p p))
                 (:instance rota-1-b13-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b13-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b13-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b13-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-13))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-13))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-13))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-13))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-13))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-13-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-13))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-13-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-13))
                                                    (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-13)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-13)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 3"
           :use ((:instance rota-1-b14-10 (p p))
                 (:instance rota-1-b14-11 (p p))
                 (:instance rota-1-b14-10-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rota-1-b14-11-1-suff (point p) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b14-10 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b14-11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rotp-rot=>b3=>rot*b3-f-or-rot-sf
                            (p (rota-inv-b3-0-n-f-1-witness p))
                            (rot (r3-m-inverse (rot-14))))
                 (:instance rot*b3-f (rot (r3-m-inverse (rot-14))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*b3-f-1 (rot (r3-m-inverse (rot-14))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f (rot (r3-m-inverse (rot-14))) (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot*set-f-1 (rot (r3-m-inverse (rot-14))) (point (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance rot-14-inv*b3-f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*b3-f-1-witness (r3-m-inverse (rot-14))
                                                   (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance rot-14-inv*f-suff (point (rota-inv-b3-0-n-f-1-witness p))
                            (p (rot*set-f-1-witness (r3-m-inverse (rot-14))
                                                    (rota-inv-b3-0-n-f-1-witness p))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-14)
                 (:instance rot-m=>rot-m-inv
                            (m (rot-14)))
                 (:instance b3-0 (p (rota-inv-b3-0-n-f-1-witness p)))
                 (:instance b3 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )

          ("subgoal 2"
           :use ((:instance rota-1-b21 (p p))
                 (:instance rota-1-b21-1-suff (p (rota-inv-b3-0-n-f-1-witness p)) (point p))
                 (:instance set-b21 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rota-1-b11 (p p))
                 (:instance rota-1-b11-1-suff (p (rota-inv-b3-0-n-f-1-witness p)) (point p))
                 (:instance set-b11 (p (rota-inv-b3-0-n-f-1-witness p)))
                 )
           :in-theory nil
           )
          ))

(defthmd rota-inv-1-14=>rota-inv-b3-0-n-f
  (implies (or (rota-1-b3-10 p)
               (rota-1-b3-11 p)
               (rota-1-b4-10 p)
               (rota-1-b4-11 p)
               (rota-1-b5-10 p)
               (rota-1-b5-11 p)
               (rota-1-b6-10 p)
               (rota-1-b6-11 p)
               (rota-1-b7-10 p)
               (rota-1-b7-11 p)
               (rota-1-b8-10 p)
               (rota-1-b8-11 p)
               (rota-1-b9-10 p)
               (rota-1-b9-11 p)
               (rota-1-b10-10 p)
               (rota-1-b10-11 p)
               (rota-1-b11-10 p)
               (rota-1-b11-11 p)
               (rota-1-b12-10 p)
               (rota-1-b12-11 p)
               (rota-1-b13-10 p)
               (rota-1-b13-11 p)
               (rota-1-b14-10 p)
               (rota-1-b14-11 p)
               (rota-1-b21 p)
               (rota-1-b11 p))
           (rota-inv-b3-0-n-f p))
  :hints (("goal"
           :cases ((rota-1-b3-10 p)
                   (rota-1-b3-11 p)
                   (rota-1-b4-10 p)
                   (rota-1-b4-11 p)
                   (rota-1-b5-10 p)
                   (rota-1-b5-11 p)
                   (rota-1-b6-10 p)
                   (rota-1-b6-11 p)
                   (rota-1-b7-10 p)
                   (rota-1-b7-11 p)
                   (rota-1-b8-10 p)
                   (rota-1-b8-11 p)
                   (rota-1-b9-10 p)
                   (rota-1-b9-11 p)
                   (rota-1-b10-10 p)
                   (rota-1-b10-11 p)
                   (rota-1-b11-10 p)
                   (rota-1-b11-11 p)
                   (rota-1-b12-10 p)
                   (rota-1-b12-11 p)
                   (rota-1-b13-10 p)
                   (rota-1-b13-11 p)
                   (rota-1-b14-10 p)
                   (rota-1-b14-11 p)
                   (rota-1-b21 p)
                   (rota-1-b11 p))
           :in-theory nil
           )
          ("subgoal 26"
           :use ((:instance rota-1-b3-10 (p p))
                 (:instance rota-1-b3-10-1 (point p))
                 (:instance b3-10 (p (rota-1-b3-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b3-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b3-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b3-10-1-witness p)))
                 ))
          ("subgoal 25"
           :use ((:instance rota-1-b3-11 (p p))
                 (:instance rota-1-b3-11-1 (point p))
                 (:instance b3-11 (p (rota-1-b3-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b3-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b3-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b3-11-1-witness p)))
                 ))
          ("subgoal 24"
           :use ((:instance rota-1-b4-10 (p p))
                 (:instance rota-1-b4-10-1 (point p))
                 (:instance b4-10 (p (rota-1-b4-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b4-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b4-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b4-10-1-witness p)))
                 )
           )
          ("subgoal 23"
           :use ((:instance rota-1-b4-11 (p p))
                 (:instance rota-1-b4-11-1 (point p))
                 (:instance b4-11 (p (rota-1-b4-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b4-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b4-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b4-11-1-witness p)))
                 )
           )
          ("subgoal 22"
           :use ((:instance rota-1-b5-10 (p p))
                 (:instance rota-1-b5-10-1 (point p))
                 (:instance b5-10 (p (rota-1-b5-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b5-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b5-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b5-10-1-witness p)))
                 )
           )
          ("subgoal 21"
           :use ((:instance rota-1-b5-11 (p p))
                 (:instance rota-1-b5-11-1 (point p))
                 (:instance b5-11 (p (rota-1-b5-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b5-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b5-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b5-11-1-witness p)))
                 )
           )
          ("subgoal 20"
           :use ((:instance rota-1-b6-10 (p p))
                 (:instance rota-1-b6-10-1 (point p))
                 (:instance b6-10 (p (rota-1-b6-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b6-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b6-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b6-10-1-witness p)))
                 )
           )
          ("subgoal 19"
           :use ((:instance rota-1-b6-11 (p p))
                 (:instance rota-1-b6-11-1 (point p))
                 (:instance b6-11 (p (rota-1-b6-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b6-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b6-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b6-11-1-witness p)))
                 )
           )

          ("subgoal 18"
           :use ((:instance rota-1-b7-10 (p p))
                 (:instance rota-1-b7-10-1 (point p))
                 (:instance b7-10 (p (rota-1-b7-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b7-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b7-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b7-10-1-witness p)))
                 )
           )
          ("subgoal 17"
           :use ((:instance rota-1-b7-11 (p p))
                 (:instance rota-1-b7-11-1 (point p))
                 (:instance b7-11 (p (rota-1-b7-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b7-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b7-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b7-11-1-witness p)))
                 )
           )

          ("subgoal 16"
           :use ((:instance rota-1-b8-10 (p p))
                 (:instance rota-1-b8-10-1 (point p))
                 (:instance b8-10 (p (rota-1-b8-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b8-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b8-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b8-10-1-witness p)))
                 )
           )
          ("subgoal 15"
           :use ((:instance rota-1-b8-11 (p p))
                 (:instance rota-1-b8-11-1 (point p))
                 (:instance b8-11 (p (rota-1-b8-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b8-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b8-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b8-11-1-witness p)))
                 )
           )
          ("subgoal 14"
           :use ((:instance rota-1-b9-10 (p p))
                 (:instance rota-1-b9-10-1 (point p))
                 (:instance b9-10 (p (rota-1-b9-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b9-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b9-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b9-10-1-witness p)))
                 )
           )
          ("subgoal 13"
           :use ((:instance rota-1-b9-11 (p p))
                 (:instance rota-1-b9-11-1 (point p))
                 (:instance b9-11 (p (rota-1-b9-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b9-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b9-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b9-11-1-witness p)))
                 )
           )
          ("subgoal 12"
           :use ((:instance rota-1-b10-10 (p p))
                 (:instance rota-1-b10-10-1 (point p))
                 (:instance b10-10 (p (rota-1-b10-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b10-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b10-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b10-10-1-witness p)))
                 )
           )
          ("subgoal 11"
           :use ((:instance rota-1-b10-11 (p p))
                 (:instance rota-1-b10-11-1 (point p))
                 (:instance b10-11 (p (rota-1-b10-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b10-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b10-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b10-11-1-witness p)))
                 )
           )
          ("subgoal 10"
           :use ((:instance rota-1-b11-10 (p p))
                 (:instance rota-1-b11-10-1 (point p))
                 (:instance b11-10 (p (rota-1-b11-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b11-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b11-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b11-10-1-witness p)))
                 )
           )
          ("subgoal 9"
           :use ((:instance rota-1-b11-11 (p p))
                 (:instance rota-1-b11-11-1 (point p))
                 (:instance b11-11 (p (rota-1-b11-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b11-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b11-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b11-11-1-witness p)))
                 )
           )
          ("subgoal 8"
           :use ((:instance rota-1-b12-10 (p p))
                 (:instance rota-1-b12-10-1 (point p))
                 (:instance b12-10 (p (rota-1-b12-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b12-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b12-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b12-10-1-witness p)))
                 )
           )
          ("subgoal 7"
           :use ((:instance rota-1-b12-11 (p p))
                 (:instance rota-1-b12-11-1 (point p))
                 (:instance b12-11 (p (rota-1-b12-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b12-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b12-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b12-11-1-witness p)))
                 )
           )
          ("subgoal 6"
           :use ((:instance rota-1-b13-10 (p p))
                 (:instance rota-1-b13-10-1 (point p))
                 (:instance b13-10 (p (rota-1-b13-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b13-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b13-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b13-10-1-witness p)))
                 )
           )
          ("subgoal 5"
           :use ((:instance rota-1-b13-11 (p p))
                 (:instance rota-1-b13-11-1 (point p))
                 (:instance b13-11 (p (rota-1-b13-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b13-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b13-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b13-11-1-witness p)))
                 )
           )
          ("subgoal 4"
           :use ((:instance rota-1-b14-10 (p p))
                 (:instance rota-1-b14-10-1 (point p))
                 (:instance b14-10 (p (rota-1-b14-10-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b14-10-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b14-10-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b14-10-1-witness p)))
                 )
           )
          ("subgoal 3"
           :use ((:instance rota-1-b14-11 (p p))
                 (:instance rota-1-b14-11-1 (point p))
                 (:instance b14-11 (p (rota-1-b14-11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b14-11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b14-11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b14-11-1-witness p)))
                 )
           )
          ("subgoal 2"
           :use ((:instance rota-1-b21 (p p))
                 (:instance rota-1-b21-1 (point p))
                 (:instance set-b21 (p (rota-1-b21-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b21-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b21-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b21-1-witness p)))
                 )
           )
          ("subgoal 1"
           :use ((:instance rota-1-b11 (p p))
                 (:instance rota-1-b11-1 (point p))
                 (:instance set-b11 (p (rota-1-b11-1-witness p)))
                 (:instance b3-0-iff-a1-to-a14 (p (rota-1-b11-1-witness p)))
                 (:instance rota-inv-b3-0-n-f (p p))
                 (:instance rota-inv-b3-0-n-f-1-suff (point p) (p (rota-1-b11-1-witness p)))
                 (:instance b3-0-n-f (p (rota-1-b11-1-witness p)))
                 )
           )))

(defthmd b3-equiv-1
  (iff (b3 p)
       (or (b3-00 p)
           (b3-01 p)
           (b4-00 p)
           (b4-01 p)
           (b5-00 p)
           (b5-01 p)
           (b6-00 p)
           (b6-01 p)
           (b7-00 p)
           (b7-01 p)
           (b8-00 p)
           (b8-01 p)
           (b9-00 p)
           (b9-01 p)
           (b10-00 p)
           (b10-01 p)
           (b11-00 p)
           (b11-01 p)
           (b12-00 p)
           (b12-01 p)
           (b13-00 p)
           (b13-01 p)
           (b14-00 p)
           (b14-01 p)
           (set-b20 p)
           (set-b10 p)
           (rota-1-b3-10 p)
           (rota-1-b3-11 p)
           (rota-1-b4-10 p)
           (rota-1-b4-11 p)
           (rota-1-b5-10 p)
           (rota-1-b5-11 p)
           (rota-1-b6-10 p)
           (rota-1-b6-11 p)
           (rota-1-b7-10 p)
           (rota-1-b7-11 p)
           (rota-1-b8-10 p)
           (rota-1-b8-11 p)
           (rota-1-b9-10 p)
           (rota-1-b9-11 p)
           (rota-1-b10-10 p)
           (rota-1-b10-11 p)
           (rota-1-b11-10 p)
           (rota-1-b11-11 p)
           (rota-1-b12-10 p)
           (rota-1-b12-11 p)
           (rota-1-b13-10 p)
           (rota-1-b13-11 p)
           (rota-1-b14-10 p)
           (rota-1-b14-11 p)
           (rota-1-b21 p)
           (rota-1-b11 p)))
  :hints (("goal"
           :use ((:instance b3-iff-b3-0-n-b3-f-or-rota-inv-b3-0-n-f (p p))
                 (:instance b3-0-n-b3-f=>1-14 (p p))
                 (:instance 1-14=>b3-0-n-b3-f (p p))
                 (:instance rota-inv-b3-0-n-f=>rota-inv-1-14 (p p))
                 (:instance rota-inv-1-14=>rota-inv-b3-0-n-f (p p))
                 )
           :in-theory nil
           )))

(defthmd b3-equiv-2
  (iff (b3 p)
       (or (rot-3-b3-00 p)
           (rot-3-b3-10 p)
           (rot-4-b4-00 p)
           (rot-4-b4-10 p)
           (rot-5-b5-00 p)
           (rot-5-b5-10 p)
           (rot-6-b6-00 p)
           (rot-6-b6-10 p)
           (rot-7-b7-00 p)
           (rot-7-b7-10 p)
           (rot-8-b8-00 p)
           (rot-8-b8-10 p)
           (rota-1-rot-3-b3-11 p)
           (rota-1-rot-3-b3-01 p)
           (rota-1-rot-4-b4-11 p)
           (rota-1-rot-4-b4-01 p)
           (rota-1-rot-5-b5-11 p)
           (rota-1-rot-5-b5-01 p)
           (rota-1-rot-6-b6-11 p)
           (rota-1-rot-6-b6-01 p)
           (rota-1-rot-7-b7-11 p)
           (rota-1-rot-7-b7-01 p)
           (rota-1-rot-8-b8-11 p)
           (rota-1-rot-8-b8-01 p)))
  :hints (("goal"
           :use ((:instance rot-3-8-b-3-8-01-or-11=>)
                 (:instance a3-a8-b3-0-n-b3-f=>)
                 (:instance rota-1-rot-3-8-b-3-8-01-or-11=>)
                 (:instance a3-a8-rot-a-inv-b3-0-nf=>)
                 (:instance b3-iff-b3-0-n-b3-f-or-rota-inv-b3-0-n-f)
                 )
           :in-theory nil
           )))

(defthmd b3-equiv-3
  (iff (b3 p)
       (or (rot-9-b9-00 p)
           (rot-9-b9-10 p)
           (rot-10-b10-00 p)
           (rot-10-b10-10 p)
           (rot-11-b11-00 p)
           (rot-11-b11-10 p)
           (rot-12-b12-00 p)
           (rot-12-b12-10 p)
           (rot-13-b13-00 p)
           (rot-13-b13-10 p)
           (rot-14-b14-00 p)
           (rot-14-b14-10 p)
           (rota-1-rot-9-b9-11 p)
           (rota-1-rot-9-b9-01 p)
           (rota-1-rot-10-b10-11 p)
           (rota-1-rot-10-b10-01 p)
           (rota-1-rot-11-b11-11 p)
           (rota-1-rot-11-b11-01 p)
           (rota-1-rot-12-b12-11 p)
           (rota-1-rot-12-b12-01 p)
           (rota-1-rot-13-b13-11 p)
           (rota-1-rot-13-b13-01 p)
           (rota-1-rot-14-b14-11 p)
           (rota-1-rot-14-b14-01 p)))
  :hints (("goal"
           :use ((:instance rot-9-14-b-9-14-01-or-11=>)
                 (:instance a9-a14-b3-0-n-b3-f=>)
                 (:instance rota-1-rot-9-14-b-9-14-01-or-11=>)
                 (:instance a9-a14-rot-a-inv-b3-0-nf=>)
                 (:instance b3-iff-b3-0-n-b3-f-or-rota-inv-b3-0-n-f)
                 )
           :in-theory nil
           )))
