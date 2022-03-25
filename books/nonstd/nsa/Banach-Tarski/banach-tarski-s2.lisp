; Banach-Tarski theorem
;
; Proof of the Banach-Tarski theorem on S^2.
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

(include-book "nonstd/nsa/trig" :dir :system)
(include-book "hausdorff-paradox-2")
(include-book "countable-sets")

(defun rotation-3d (angle point)
  `((:header :dimensions (3 3)
             :maximum-length 10)
    ((0 . 0) . ,(+ (acl2-cosine angle)
                   (* (point-in-r3-x1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))) )
    ((0 . 1) . ,(- (* (point-in-r3-x1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-z1 point) (acl2-sine angle))) )
    ((0 . 2) . ,(+ (* (point-in-r3-x1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-y1 point) (acl2-sine angle))) )
    ((1 . 0) . ,(+ (* (point-in-r3-y1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-z1 point) (acl2-sine angle))) )
    ((1 . 1) . ,(+ (acl2-cosine angle)
                   (* (point-in-r3-y1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))) )
    ((1 . 2) . ,(- (* (point-in-r3-y1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-x1 point) (acl2-sine angle))) )
    ((2 . 0) . ,(- (* (point-in-r3-z1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-y1 point) (acl2-sine angle))) )
    ((2 . 1) . ,(+ (* (point-in-r3-z1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                   (* (point-in-r3-x1 point) (acl2-sine angle))) )
    ((2 . 2) . ,(+ (acl2-cosine angle)
                   (* (point-in-r3-z1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))) )
    )
  )

(defthmd rotation-about-witness-values
  (and (equal (aref2 :fake-name (rotation-3d angle point) 0 0)
              (+ (acl2-cosine angle)
                 (* (point-in-r3-x1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))))
       (equal (aref2 :fake-name (rotation-3d angle point) 0 1)
              (- (* (point-in-r3-x1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-z1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-3d angle point) 0 2)
              (+ (* (point-in-r3-x1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-y1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-3d angle point) 1 0)
              (+ (* (point-in-r3-y1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-z1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-3d angle point) 1 1)
              (+ (acl2-cosine angle)
                 (* (point-in-r3-y1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))))
       (equal (aref2 :fake-name (rotation-3d angle point) 1 2)
              (- (* (point-in-r3-y1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-x1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-3d angle point) 2 0)
              (- (* (point-in-r3-z1 point) (point-in-r3-x1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-y1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-3d angle point) 2 1)
              (+ (* (point-in-r3-z1 point) (point-in-r3-y1 point) (- 1 (acl2-cosine angle)))
                 (* (point-in-r3-x1 point) (acl2-sine angle))))
       (equal (aref2 :fake-name (rotation-3d angle point) 2 2)
              (+ (acl2-cosine angle)
                 (* (point-in-r3-z1 point) (point-in-r3-z1 point) (- 1 (acl2-cosine angle)))))
       )
  :hints (("goal"
           :in-theory (enable aref2)
           ))
  )

(defthmd r3-matrixp-r3d
  (implies (and (realp angle)
                (point-in-r3 u))
           (r3-matrixp (rotation-3d angle u)))
  :hints (("goal"
           :in-theory (enable aref2 header dimensions array2p)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-lemma1
   (iff (equal (+ (* s s) (* c c)) 1)
	(equal (* s s) (- 1 (* c c)))))

 (defthmd r3-rotationp-r-theta-11-1-lemma2
   (equal (- a (* a c)) (* a (- 1 c))))

 (defthmd r3-rotationp-r-theta-11-1-lemma3
   (equal (+ (* c a) (* b a))
	  (+ (* a (+ b c)))))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-00-lemma1
   (equal (+ (* d a) (* d b) (* d c))
	  (* d (+ a b c))))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-00-lemma2
   (iff (equal (+ (* x x) (* y y) (* z z)) 1)
	(equal (+ (* y y) (* z z)) (- 1 (* x x)))))

 (defthmd r3-rotationp-r-theta-11-1-lemma4
   (implies (point-in-r3 p)
	    (and (realp (point-in-r3-x1 p))
		 (realp (point-in-r3-y1 p))
		 (realp (point-in-r3-z1 p)))))
 )

(defthmd witness-not-in-x-coord-sequence-1
  (and (realp (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))
       (realp (acl2-sqrt (- 1 (* (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)
                                 (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)))))
       (<= -1 (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))
       (<= (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1) 1))
  :hints (("goal"
           :use ((:instance witness-not-in-x-coord-sequence)
                 (:instance exists-point-on-s2-not-d-2))
           )))

(defthmd r3-rotationp-r-theta-8
  (implies (realp angle)
           (and (realp (acl2-sine angle))
                (realp (acl2-cosine angle)))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-10
   (implies (and (realp angle)
		 (point-in-r3 p))
	    (r3-matrixp (rotation-3d angle p)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-8)
		  (:instance rotation-about-witness-values (angle angle) (point p)))
	    :in-theory (e/d (header dimensions default array2p) (aref2))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-00
   (implies (and (realp c1)
		 (realp c2)
		 (realp x)
		 (realp y)
		 (realp z)
		 (realp s1)
		 (realp s2)
		 (equal m1-00 (+ c1 (* x x (- 1 c1))))
		 (equal m2-00 (+ c2 (* x x (- 1 c2))))
		 (equal m1-01 (- (* x y (- 1 c1)) (* z s1)))
		 (equal m2-10 (+ (* y x (- 1 c2)) (* z s2)))
		 (equal m1-02 (+ (* x z (- 1 c1)) (* y s1)))
		 (equal m2-20 (- (* z x (- 1 c2)) (* y s2)))
		 (equal m3-00 (+ cosc1c2 (* x x (- 1 cosc1c2))))
		 (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
		 (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* s1 s1) (* c1 c1)) 1)
		 (equal (+ (* s2 s2) (* c2 c2)) 1))
	    (equal (+ (* m1-00 m2-00)
		      (* m1-01 m2-10)
		      (* m1-02 m2-20)
		      )
		   m3-00))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c1 x x)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c2 x x)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* x x))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* c1 c2 x x))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r3-rotationp-r-theta-11-1-lemma3
			     (a (- (* s1 s2)))
			     (c (* y y))
			     (b (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma2 (x x) (y y) (z z))
		  )
	    )))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-01
   (implies (and (realp c1)
		 (realp c2)
		 (realp x)
		 (realp y)
		 (realp z)
		 (realp s1)
		 (realp s2)
		 (equal m1-00 (+ c1 (* x x (- 1 c1))))
		 (equal m1-01 (- (* x y (- 1 c1)) (* z s1)))
		 (equal m1-02 (+ (* x z (- 1 c1)) (* y s1)))
		 (equal m2-01 (- (* x y (- 1 c2)) (* z s2)))
		 (equal m2-11 (+ c2 (* y y (- 1 c2))))
		 (equal m2-21 (+ (* z y (- 1 c2)) (* x s2)))
		 (equal m3-01 (- (* x y (- 1 cosc1c2)) (* z sins1s2)))
		 (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
		 (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* s1 s1) (* c1 c1)) 1)
		 (equal (+ (* s2 s2) (* c2 c2)) 1))
	    (equal (+ (* m1-00 m2-01)
		      (* m1-01 m2-11)
		      (* m1-02 m2-21)
		      )
		   m3-01))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c1 x y)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c2 x y)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* x y))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* c1 c2 x y))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  )
	    )))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-02
   (implies (and (realp c1)
		 (realp c2)
		 (realp x)
		 (realp y)
		 (realp z)
		 (realp s1)
		 (realp s2)
		 (equal m1-00 (+ c1 (* x x (- 1 c1))))
		 (equal m1-01 (- (* x y (- 1 c1)) (* z s1)))
		 (equal m1-02 (+ (* x z (- 1 c1)) (* y s1)))
		 (equal m2-02 (+ (* x z (- 1 c2)) (* y s2)))
		 (equal m2-12 (- (* y z (- 1 c2)) (* x s2)))
		 (equal m2-22 (+ c2 (* z z (- 1 c2))))
		 (equal m3-02 (+ (* x z (- 1 cosc1c2)) (* y sins1s2)))
		 (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
		 (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* s1 s1) (* c1 c1)) 1)
		 (equal (+ (* s2 s2) (* c2 c2)) 1))
	    (equal (+ (* m1-00 m2-02)
		      (* m1-01 m2-12)
		      (* m1-02 m2-22)
		      )
		   m3-02))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c1 x z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c2 x z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* x z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* c1 c2 x z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  )
	    )))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-10
   (implies (and (realp c1)
		 (realp c2)
		 (realp x)
		 (realp y)
		 (realp z)
		 (realp s1)
		 (realp s2)
		 (equal m1-10 (+ (* y x (- 1 c1)) (* z s1)))
		 (equal m1-11 (+ c1 (* y y (- 1 c1))))
		 (equal m1-12 (- (* y z (- 1 c1)) (* x s1)))
		 (equal m2-00 (+ c2 (* x x (- 1 c2))))
		 (equal m2-10 (+ (* y x (- 1 c2)) (* z s2)))
		 (equal m2-20 (- (* z x (- 1 c2)) (* y s2)))
		 (equal m3-10 (+ (* y x (- 1 cosc1c2)) (* z sins1s2)))
		 (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
		 (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* s1 s1) (* c1 c1)) 1)
		 (equal (+ (* s2 s2) (* c2 c2)) 1))
	    (equal (+ (* m1-10 m2-00)
		      (* m1-11 m2-10)
		      (* m1-12 m2-20)
		      )
		   m3-10))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c1 x y)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c2 x y)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* x y))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* c1 c2 x y))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  )
	    )))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-11
   (implies (and (realp c1)
		 (realp c2)
		 (realp x)
		 (realp y)
		 (realp z)
		 (realp s1)
		 (realp s2)
		 (equal m1-10 (+ (* y x (- 1 c1)) (* z s1)))
		 (equal m1-11 (+ c1 (* y y (- 1 c1))))
		 (equal m1-12 (- (* y z (- 1 c1)) (* x s1)))
		 (equal m2-01 (- (* x y (- 1 c2)) (* z s2)))
		 (equal m2-11 (+ c2 (* y y (- 1 c2))))
		 (equal m2-21 (+ (* z y (- 1 c2)) (* x s2)))
		 (equal m3-11 (+ cosc1c2 (* y y (- 1 cosc1c2))))
		 (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
		 (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* s1 s1) (* c1 c1)) 1)
		 (equal (+ (* s2 s2) (* c2 c2)) 1))
	    (equal (+ (* m1-10 m2-01)
		      (* m1-11 m2-11)
		      (* m1-12 m2-21)
		      )
		   m3-11))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c1 y y)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c2 y y)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* y y))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* c1 c2 y y))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  )
	    )))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-12
   (implies (and (realp c1)
		 (realp c2)
		 (realp x)
		 (realp y)
		 (realp z)
		 (realp s1)
		 (realp s2)
		 (equal m1-10 (+ (* y x (- 1 c1)) (* z s1)))
		 (equal m1-11 (+ c1 (* y y (- 1 c1))))
		 (equal m1-12 (- (* y z (- 1 c1)) (* x s1)))
		 (equal m2-02 (+ (* x z (- 1 c2)) (* y s2)))
		 (equal m2-12 (- (* y z (- 1 c2)) (* x s2)))
		 (equal m2-22 (+ c2 (* z z (- 1 c2))))
		 (equal m3-12 (- (* y z (- 1 cosc1c2)) (* x sins1s2)))
		 (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
		 (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* s1 s1) (* c1 c1)) 1)
		 (equal (+ (* s2 s2) (* c2 c2)) 1))
	    (equal (+ (* m1-10 m2-02)
		      (* m1-11 m2-12)
		      (* m1-12 m2-22)
		      )
		   m3-12))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c1 y z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c2 y z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* y z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* c1 c2 y z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  )
	    )))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-20
   (implies (and (realp c1)
		 (realp c2)
		 (realp x)
		 (realp y)
		 (realp z)
		 (realp s1)
		 (realp s2)
		 (equal m1-20 (- (* z x (- 1 c1)) (* y s1)))
		 (equal m1-21 (+ (* z y (- 1 c1)) (* x s1)))
		 (equal m1-22 (+ c1 (* z z (- 1 c1))))
		 (equal m2-00 (+ c2 (* x x (- 1 c2))))
		 (equal m2-10 (+ (* y x (- 1 c2)) (* z s2)))
		 (equal m2-20 (- (* z x (- 1 c2)) (* y s2)))
		 (equal m3-20 (- (* z x (- 1 cosc1c2)) (* y sins1s2)))
		 (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
		 (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* s1 s1) (* c1 c1)) 1)
		 (equal (+ (* s2 s2) (* c2 c2)) 1))
	    (equal (+ (* m1-20 m2-00)
		      (* m1-21 m2-10)
		      (* m1-22 m2-20)
		      )
		   m3-20))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c1 x z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c2 x z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* x z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* c1 c2 x z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  )
	    )))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-21
   (implies (and (realp c1)
		 (realp c2)
		 (realp x)
		 (realp y)
		 (realp z)
		 (realp s1)
		 (realp s2)
		 (equal m1-20 (- (* z x (- 1 c1)) (* y s1)))
		 (equal m1-21 (+ (* z y (- 1 c1)) (* x s1)))
		 (equal m1-22 (+ c1 (* z z (- 1 c1))))
		 (equal m2-01 (- (* x y (- 1 c2)) (* z s2)))
		 (equal m2-11 (+ c2 (* y y (- 1 c2))))
		 (equal m2-21 (+ (* z y (- 1 c2)) (* x s2)))
		 (equal m3-21 (+ (* z y (- 1 cosc1c2)) (* x sins1s2)))
		 (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
		 (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* s1 s1) (* c1 c1)) 1)
		 (equal (+ (* s2 s2) (* c2 c2)) 1))
	    (equal (+ (* m1-20 m2-01)
		      (* m1-21 m2-11)
		      (* m1-22 m2-21)
		      )
		   m3-21))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c1 y z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c2 y z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* y z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* c1 c2 y z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  )
	    )))

 (defthmd r-t1*r-t2=r-t1+t2-m-*-22
   (implies (and (realp c1)
		 (realp c2)
		 (realp x)
		 (realp y)
		 (realp z)
		 (realp s1)
		 (realp s2)
		 (equal m1-20 (- (* z x (- 1 c1)) (* y s1)))
		 (equal m1-21 (+ (* z y (- 1 c1)) (* x s1)))
		 (equal m1-22 (+ c1 (* z z (- 1 c1))))
		 (equal m2-02 (+ (* x z (- 1 c2)) (* y s2)))
		 (equal m2-12 (- (* y z (- 1 c2)) (* x s2)))
		 (equal m2-22 (+ c2 (* z z (- 1 c2))))
		 (equal m3-22 (+ cosc1c2 (* z z (- 1 cosc1c2))))
		 (equal cosc1c2 (- (* c1 c2) (* s1 s2)))
		 (equal sins1s2 (+ (* s1 c2) (* c1 s2)))
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* s1 s1) (* c1 c1)) 1)
		 (equal (+ (* s2 s2) (* c2 c2)) 1))
	    (equal (+ (* m1-20 m2-02)
		      (* m1-21 m2-12)
		      (* m1-22 m2-22)
		      )
		   m3-22))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c1 z z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (- (* c2 z z)))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* z z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  (:instance r-t1*r-t2=r-t1+t2-m-*-00-lemma1
			     (d (* c1 c2 z z))
			     (a (* x x))
			     (b (* y y))
			     (c (* z z)))
		  )
	    )))
 )

(defthmd m-=-equiv-lemma
  (implies (and (r3-matrixp m1)
                (r3-matrixp m2)
                (equal (aref2 :fake-name m1 0 0) (aref2 :fake-name m2 0 0))
                (equal (aref2 :fake-name m1 0 1) (aref2 :fake-name m2 0 1))
                (equal (aref2 :fake-name m1 0 2) (aref2 :fake-name m2 0 2))
                (equal (aref2 :fake-name m1 1 0) (aref2 :fake-name m2 1 0))
                (equal (aref2 :fake-name m1 1 1) (aref2 :fake-name m2 1 1))
                (equal (aref2 :fake-name m1 1 2) (aref2 :fake-name m2 1 2))
                (equal (aref2 :fake-name m1 2 0) (aref2 :fake-name m2 2 0))
                (equal (aref2 :fake-name m1 2 1) (aref2 :fake-name m2 2 1))
                (equal (aref2 :fake-name m1 2 2) (aref2 :fake-name m2 2 2))
                )
           (m-= m1 m2))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd r-t1*r-t2=r-t1+t2
  (implies (and (realp angle1)
                (realp angle2)
                (point-in-r3 u)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1))
           (m-= (m-* (rotation-3d angle1 u)
                     (rotation-3d angle2 u))
                (rotation-3d (+ angle1 angle2) u)))
  :hints (("goal"
           :use ((:instance r3-rotationp-r-theta-10 (angle angle1) (p u))
                 (:instance r3-rotationp-r-theta-10 (angle angle2) (p u))
                 (:instance r3-rotationp-r-theta-10 (angle (+ angle1 angle2)) (p u))
                 (:instance r3-matrixp (m (rotation-3d angle1 u)))
                 (:instance r3-matrixp (m (rotation-3d angle2 u)))
                 (:instance r3-matrixp (m (rotation-3d (+ angle1 angle2) u)))
                 (:instance sine-of-sums (x angle1) (y angle2))
                 (:instance cosine-of-sums (x angle1) (y angle2))
                 (:instance sin**2+cos**2 (x angle1))
                 (:instance sin**2+cos**2 (x angle2))
                 (:instance r3-rotationp-r-theta-11-1-lemma4 (p u))
                 (:instance r3-rotationp-r-theta-8 (angle angle1))
                 (:instance r3-rotationp-r-theta-8 (angle angle2))
                 (:instance rotation-about-witness-values (point u) (angle angle1))
                 (:instance rotation-about-witness-values (point u) (angle angle2))
                 (:instance rotation-about-witness-values (point u) (angle (+ angle1 angle2)))
                 (:instance aref2-m-*
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u))
                            (name :fake-name)
                            (i 0)
                            (j 0))
                 (:instance aref2-m-*
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u))
                            (name :fake-name)
                            (i 0)
                            (j 1))
                 (:instance aref2-m-*
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u))
                            (name :fake-name)
                            (i 0)
                            (j 2))
                 (:instance aref2-m-*
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u))
                            (name :fake-name)
                            (i 1)
                            (j 0))
                 (:instance aref2-m-*
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u))
                            (name :fake-name)
                            (i 1)
                            (j 1))
                 (:instance aref2-m-*
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u))
                            (name :fake-name)
                            (i 1)
                            (j 2))
                 (:instance aref2-m-*
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u))
                            (name :fake-name)
                            (i 2)
                            (j 0))
                 (:instance aref2-m-*
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u))
                            (name :fake-name)
                            (i 2)
                            (j 1))
                 (:instance aref2-m-*
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u))
                            (name :fake-name)
                            (i 2)
                            (j 2))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-00
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (m1-00 (aref2 :fake-name (rotation-3d angle1 u) 0 0))
                            (m1-01 (aref2 :fake-name (rotation-3d angle1 u) 0 1))
                            (m1-02 (aref2 :fake-name (rotation-3d angle1 u) 0 2))
                            (m2-00 (aref2 :fake-name (rotation-3d angle2 u) 0 0))
                            (m2-10 (aref2 :fake-name (rotation-3d angle2 u) 1 0))
                            (m2-20 (aref2 :fake-name (rotation-3d angle2 u) 2 0))
                            (m3-00 (aref2 :fake-name (rotation-3d (+ angle1 angle2) u) 0 0))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-01
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-00 (aref2 :fake-name (rotation-3d angle1 u) 0 0))
                            (m1-01 (aref2 :fake-name (rotation-3d angle1 u) 0 1))
                            (m1-02 (aref2 :fake-name (rotation-3d angle1 u) 0 2))
                            (m2-01 (aref2 :fake-name (rotation-3d angle2 u) 0 1))
                            (m2-11 (aref2 :fake-name (rotation-3d angle2 u) 1 1))
                            (m2-21 (aref2 :fake-name (rotation-3d angle2 u) 2 1))
                            (m3-01 (aref2 :fake-name (rotation-3d (+ angle1 angle2) u) 0 1))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-02
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-00 (aref2 :fake-name (rotation-3d angle1 u) 0 0))
                            (m1-01 (aref2 :fake-name (rotation-3d angle1 u) 0 1))
                            (m1-02 (aref2 :fake-name (rotation-3d angle1 u) 0 2))
                            (m2-02 (aref2 :fake-name (rotation-3d angle2 u) 0 2))
                            (m2-12 (aref2 :fake-name (rotation-3d angle2 u) 1 2))
                            (m2-22 (aref2 :fake-name (rotation-3d angle2 u) 2 2))
                            (m3-02 (aref2 :fake-name (rotation-3d (+ angle1 angle2) u) 0 2))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-10
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-10 (aref2 :fake-name (rotation-3d angle1 u) 1 0))
                            (m1-11 (aref2 :fake-name (rotation-3d angle1 u) 1 1))
                            (m1-12 (aref2 :fake-name (rotation-3d angle1 u) 1 2))
                            (m2-00 (aref2 :fake-name (rotation-3d angle2 u) 0 0))
                            (m2-10 (aref2 :fake-name (rotation-3d angle2 u) 1 0))
                            (m2-20 (aref2 :fake-name (rotation-3d angle2 u) 2 0))
                            (m3-10 (aref2 :fake-name (rotation-3d (+ angle1 angle2) u) 1 0))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-11
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-10 (aref2 :fake-name (rotation-3d angle1 u) 1 0))
                            (m1-11 (aref2 :fake-name (rotation-3d angle1 u) 1 1))
                            (m1-12 (aref2 :fake-name (rotation-3d angle1 u) 1 2))
                            (m2-01 (aref2 :fake-name (rotation-3d angle2 u) 0 1))
                            (m2-11 (aref2 :fake-name (rotation-3d angle2 u) 1 1))
                            (m2-21 (aref2 :fake-name (rotation-3d angle2 u) 2 1))
                            (m3-11 (aref2 :fake-name (rotation-3d (+ angle1 angle2) u) 1 1))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-12
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-10 (aref2 :fake-name (rotation-3d angle1 u) 1 0))
                            (m1-11 (aref2 :fake-name (rotation-3d angle1 u) 1 1))
                            (m1-12 (aref2 :fake-name (rotation-3d angle1 u) 1 2))
                            (m2-02 (aref2 :fake-name (rotation-3d angle2 u) 0 2))
                            (m2-12 (aref2 :fake-name (rotation-3d angle2 u) 1 2))
                            (m2-22 (aref2 :fake-name (rotation-3d angle2 u) 2 2))
                            (m3-12 (aref2 :fake-name (rotation-3d (+ angle1 angle2) u) 1 2))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-20
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-20 (aref2 :fake-name (rotation-3d angle1 u) 2 0))
                            (m1-21 (aref2 :fake-name (rotation-3d angle1 u) 2 1))
                            (m1-22 (aref2 :fake-name (rotation-3d angle1 u) 2 2))
                            (m2-00 (aref2 :fake-name (rotation-3d angle2 u) 0 0))
                            (m2-10 (aref2 :fake-name (rotation-3d angle2 u) 1 0))
                            (m2-20 (aref2 :fake-name (rotation-3d angle2 u) 2 0))
                            (m3-20 (aref2 :fake-name (rotation-3d (+ angle1 angle2) u) 2 0))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-21
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-20 (aref2 :fake-name (rotation-3d angle1 u) 2 0))
                            (m1-21 (aref2 :fake-name (rotation-3d angle1 u) 2 1))
                            (m1-22 (aref2 :fake-name (rotation-3d angle1 u) 2 2))
                            (m2-01 (aref2 :fake-name (rotation-3d angle2 u) 0 1))
                            (m2-11 (aref2 :fake-name (rotation-3d angle2 u) 1 1))
                            (m2-21 (aref2 :fake-name (rotation-3d angle2 u) 2 1))
                            (m3-21 (aref2 :fake-name (rotation-3d (+ angle1 angle2) u) 2 1))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance r-t1*r-t2=r-t1+t2-m-*-22
                            (c1 (acl2-cosine angle1))
                            (c2 (acl2-cosine angle2))
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (m1-20 (aref2 :fake-name (rotation-3d angle1 u) 2 0))
                            (m1-21 (aref2 :fake-name (rotation-3d angle1 u) 2 1))
                            (m1-22 (aref2 :fake-name (rotation-3d angle1 u) 2 2))
                            (m2-02 (aref2 :fake-name (rotation-3d angle2 u) 0 2))
                            (m2-12 (aref2 :fake-name (rotation-3d angle2 u) 1 2))
                            (m2-22 (aref2 :fake-name (rotation-3d angle2 u) 2 2))
                            (m3-22 (aref2 :fake-name (rotation-3d (+ angle1 angle2) u) 2 2))
                            (s1 (acl2-sine angle1))
                            (s2 (acl2-sine angle2))
                            (cosc1c2 (acl2-cosine (+ angle1 angle2)))
                            (sins1s2 (acl2-sine (+ angle1 angle2))))
                 (:instance m-=-equiv-lemma
                            (m1 (m-* (rotation-3d angle1 u)
                                     (rotation-3d angle2 u)))
                            (m2 (rotation-3d (+ angle1 angle2) u)))
                 (:instance r3-matrixp-m1*m2-is-r3-matrixp
                            (m1 (rotation-3d angle1 u))
                            (m2 (rotation-3d angle2 u)))
                 )
           :in-theory (e/d () (m-= aref2 m-* point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-= sine-of-sums cosine-of-sums aref2-m-* r3-matrixp-m1*m2-is-r3-matrixp))

           )
          ))

(defthmd r3-rotationp-r-theta-2-1
  (equal
   (*
    (acl2-sqrt
     (+
      1
      (- (* (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)
            (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)))))
    (acl2-sqrt
     (+
      1
      (-
       (* (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)
          (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1))))))
   (+
    1
    (- (* (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)
          (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)))))
  :hints (("goal"
           :use ((:instance exists-point-on-s2-not-d-1-4
                            (p (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)))
                 (:instance witness-not-in-x-coord-sequence-1)
                 (:instance sqrt-sqrt
                            (x (+
                                1
                                (- (* (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)
                                      (exists-in-interval-but-not-in-x-coord-sequence-witness -1 1)))))))
           :in-theory nil
           )))

(defthmd r3-rotationp-r-theta-2
  (implies (equal (point-on-s2-not-d) point)
           (equal (+ (* (point-in-r3-x1 point) (point-in-r3-x1 point))
                     (* (point-in-r3-z1 point) (point-in-r3-z1 point)))
                  1))
  :hints (("goal"
           :use ((:instance r3-rotationp-r-theta-2-1))
           :in-theory (enable aref2)
           )))

(defthmd r3-rotationp-r-theta-3
  (implies (equal (point-on-s2-not-d) point)
           (equal (* (point-in-r3-x1 point) (point-in-r3-x1 point))
                  (- 1 (* (point-in-r3-z1 point) (point-in-r3-z1 point)))))
  :hints (("goal"
           :use (:instance r3-rotationp-r-theta-2)
           )))

(defthmd r3-rotationp-r-theta-4
  (implies (equal (point-on-s2-not-d) point)
           (equal (* (point-in-r3-z1 point) (point-in-r3-z1 point))
                  (- 1 (* (point-in-r3-x1 point) (point-in-r3-x1 point)))))
  :hints (("goal"
           :use (:instance r3-rotationp-r-theta-2)
           )))

(defthmd r3-rotationp-r-theta-5
  (implies (equal (point-on-s2-not-d) point)
           (and (realp (point-in-r3-x1 point))
                (realp (point-in-r3-z1 point))
                (equal (point-in-r3-y1 point) 0)))
  :hints (("goal"
           :use ((:instance exists-point-on-s2-not-d-2))
           :in-theory (enable aref2)
           )))

(defthmd r3-rotationp-r-theta-6
  (equal (* (acl2-sine x) (acl2-sine x))
         (- 1 (* (acl2-cosine x) (acl2-cosine x))))
  :hints (("goal"
           :use (:instance sin**2+cos**2 (x x))
           :in-theory (disable sin**2+cos**2)
           )))

(defthmd r3-rotationp-r-theta-7
  (equal (* (acl2-cosine x) (acl2-cosine x))
         (- 1 (* (acl2-sine x) (acl2-sine x))))
  :hints (("goal"
           :use (:instance sin**2+cos**2 (x x))
           :in-theory (disable sin**2+cos**2)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-9-1-1
   (implies (and (realp x)
		 (realp z)
		 (equal (+ (expt x 2) (expt z 2)) 1))
	    (equal (* (+ (* x x) (* z z))
		      (+ (* x x) (* z z)))
		   1))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-9-1-2
   (equal (+ (expt x 4)
	     (expt z 4)
	     (* 2 (expt x 2) (expt z 2)))
	  (* (+ (* x x) (* z z))
	     (+ (* x x) (* z z)))
	  )))

(defthmd r3-rotationp-r-theta-9-1-3
  (implies (and (realp x)
                (realp z)
                (equal (+ (expt x 2) (expt z 2)) 1)
                (not (equal z 0))
                (not (equal x 0)))
           (equal (+ (expt x 4)
                     (expt z 4)
                     (* 2 (expt x 2) (expt z 2)))
                  1))
  :hints (("goal"
           :use ((:instance r3-rotationp-r-theta-9-1-1)
                 (:instance r3-rotationp-r-theta-9-1-2))
           :in-theory nil
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-9-1-4
   (equal (+ 1 (* (expt x 2) (expt c 3))
	     (* (expt z 2) (expt c 3))
	     (* c (expt s 2) (expt x 4))
	     (* c (expt s 2) (expt z 4))
	     (* 2 c (expt s 2)
		(expt x 2)
		(expt z 2)))
	  (+ 1
	     (* (expt c 3) (+ (expt x 2) (expt z 2)))
	     (* c (expt s 2) (+ (expt x 4) (expt z 4) (* 2 (expt x 2) (expt z 2)))))))

 (defthmd r3-rotationp-r-theta-9-1-5
   (equal (+ (expt c 3)
	     (* (expt c 2) (expt x 2))
	     (* (expt c 2) (expt z 2))
	     (* (expt s 2) (expt x 4))
	     (* (expt s 2) (expt z 4))
	     (* c (expt s 2) (expt x 2))
	     (* c (expt s 2) (expt z 2))
	     (* 2 (expt s 2) (expt x 2) (expt z 2)))
	  (+ (expt c 3)
	     (* (expt c 2) (+ (expt x 2) (expt z 2)))
	     (* c (expt s 2) (+ (expt x 2) (expt z 2)))
	     (* (expt s 2) (+ (expt x 4) (expt z 4) (* 2 (expt x 2) (expt z 2)))))))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-9-1
   (implies (and (realp x)
		 (realp z)
		 (realp c)
		 (realp s)
		 (equal (+ (* x x) (* z z)) 1)
		 (equal (+ (* s s) (* c c)) 1))
	    (equal (+ (* x
			 x
			 z
			 z
			 c)
		      (- (* x
			    x
			    z
			    z
			    c))
		      (* x
			 x
			 c
			 c)
		      (* z
			 z
			 c
			 c)
		      (* x
			 x
			 x
			 x
			 s
			 s)
		      (* x
			 x
			 z
			 z
			 c
			 c)
		      (* x
			 x
			 z
			 z
			 c
			 c)
		      (- (* x
			    x
			    z
			    z
			    c
			    c))
		      (- (* x
			    x
			    z
			    z
			    c
			    c))
		      (* x
			 x
			 z
			 z
			 s
			 s)
		      (* x
			 x
			 z
			 z
			 s
			 s)
		      (* z
			 z
			 z
			 z
			 s
			 s)
		      (* c
			 c
			 c)
		      (- (* x
			    x
			    c
			    c
			    c))
		      (* x
			 x
			 c
			 s
			 s)
		      (- (* z
			    z
			    c
			    c
			    c))
		      (* z
			 z
			 c
			 s
			 s)
		      (- (* x
			    x
			    x
			    x
			    c
			    s
			    s))
		      (* x
			 x
			 z
			 z
			 c
			 c
			 c)
		      (- (* x
			    x
			    z
			    z
			    c
			    c
			    c))
		      (- (* x
			    x
			    z
			    z
			    c
			    s
			    s))
		      (- (* x
			    x
			    z
			    z
			    c
			    s
			    s))
		      (- (* z
			    z
			    z
			    z
			    c
			    s
			    s)))
		   1))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-9-1-1)
		  (:instance r3-rotationp-r-theta-9-1-3))
	    )
	   ("subgoal 1"
	    :use ((:instance r3-rotationp-r-theta-9-1-4)
		  (:instance r3-rotationp-r-theta-9-1-5))
	    )
	   ))
 )

(defthmd r3-rotationp-r-theta-9
  (implies (realp angle)
           (equal (+ (* (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (acl2-cosine angle))
                     (- (* (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (acl2-cosine angle)))
                     (* (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (acl2-cosine angle)
                        (acl2-cosine angle))
                     (* (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (acl2-cosine angle)
                        (acl2-cosine angle))
                     (* (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (acl2-sine angle)
                        (acl2-sine angle))
                     (* (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (acl2-cosine angle)
                        (acl2-cosine angle))
                     (* (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (acl2-cosine angle)
                        (acl2-cosine angle))
                     (- (* (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (acl2-cosine angle)
                           (acl2-cosine angle)))
                     (- (* (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (acl2-cosine angle)
                           (acl2-cosine angle)))
                     (* (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (acl2-sine angle)
                        (acl2-sine angle))
                     (* (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (acl2-sine angle)
                        (acl2-sine angle))
                     (* (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (acl2-sine angle)
                        (acl2-sine angle))
                     (* (acl2-cosine angle)
                        (acl2-cosine angle)
                        (acl2-cosine angle))
                     (- (* (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (acl2-cosine angle)
                           (acl2-cosine angle)
                           (acl2-cosine angle)))
                     (* (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (acl2-cosine angle)
                        (acl2-sine angle)
                        (acl2-sine angle))
                     (- (* (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (acl2-cosine angle)
                           (acl2-cosine angle)
                           (acl2-cosine angle)))
                     (* (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (acl2-cosine angle)
                        (acl2-sine angle)
                        (acl2-sine angle))
                     (- (* (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (acl2-cosine angle)
                           (acl2-sine angle)
                           (acl2-sine angle)))
                     (* (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-x1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (point-in-r3-z1 (point-on-s2-not-d))
                        (acl2-cosine angle)
                        (acl2-cosine angle)
                        (acl2-cosine angle))
                     (- (* (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (acl2-cosine angle)
                           (acl2-cosine angle)
                           (acl2-cosine angle)))
                     (- (* (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (acl2-cosine angle)
                           (acl2-sine angle)
                           (acl2-sine angle)))
                     (- (* (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-x1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (acl2-cosine angle)
                           (acl2-sine angle)
                           (acl2-sine angle)))
                     (- (* (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (point-in-r3-z1 (point-on-s2-not-d))
                           (acl2-cosine angle)
                           (acl2-sine angle)
                           (acl2-sine angle))))
                  1))
  :hints (("goal"
           :use ((:instance r3-rotationp-r-theta-9-1
                            (x (point-in-r3-x1 (point-on-s2-not-d)))
                            (z (point-in-r3-z1 (point-on-s2-not-d)))
                            (s (acl2-sine angle))
                            (c (acl2-cosine angle)))
                 (:instance r3-rotationp-r-theta-8)
                 (:instance sin**2+cos**2 (x angle))
                 (:instance r3-rotationp-r-theta-2 (point (point-on-s2-not-d)))
                 (:instance r3-rotationp-r-theta-5 (point (point-on-s2-not-d))))
           )))

(encapsulate
 ()

 (local (in-theory nil))

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-1
   (implies (realp angle)
	    (equal (r3-m-determinant (rotation-3d angle (point-on-s2-not-d)))
		   1))
   :hints (("goal"
	    :use ((:instance rotation-about-witness-values (angle angle) (point (point-on-s2-not-d)))
		  (:instance r3-rotationp-r-theta-2 (point (point-on-s2-not-d)))
		  (:instance r3-rotationp-r-theta-3 (point (point-on-s2-not-d)))
		  (:instance r3-rotationp-r-theta-4 (point (point-on-s2-not-d)))
		  (:instance r3-rotationp-r-theta-5 (point (point-on-s2-not-d)))
		  (:instance r3-rotationp-r-theta-9)
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-rotationp-r-theta-8)
		  (:instance r3-rotationp-r-theta-6 (x angle)))
	    :in-theory (e/d (r3-m-determinant header default dimensions rotation-3d) (point-on-s2-not-d acl2-sqrt point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 sin**2+cos**2 aref2))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-matrixp-r3-m-inverse
   (implies (r3-matrixp m)
	    (r3-matrixp (r3-m-inverse m)))
   :hints (("goal"
	    :use ((:instance r3-m-inverse-= (m m)))
	    :in-theory (e/d (array2p) (aref2 r3-m-inverse-=))
	    )))

 (defthmd r3-matrixp-m-trans
   (implies (r3-matrixp m)
	    (r3-matrixp (m-trans m))))

 (defthmd m-trans-values
   (implies (r3-matrixp m)
	    (and (equal (aref2 :fake-name (m-trans m) 0 0)
			(aref2 :fake-name m 0 0))
		 (equal (aref2 :fake-name (m-trans m) 0 1)
			(aref2 :fake-name m 1 0))
		 (equal (aref2 :fake-name (m-trans m) 0 2)
			(aref2 :fake-name m 2 0))
		 (equal (aref2 :fake-name (m-trans m) 1 0)
			(aref2 :fake-name m 0 1))
		 (equal (aref2 :fake-name (m-trans m) 1 1)
			(aref2 :fake-name m 1 1))
		 (equal (aref2 :fake-name (m-trans m) 1 2)
			(aref2 :fake-name m 2 1))
		 (equal (aref2 :fake-name (m-trans m) 2 0)
			(aref2 :fake-name m 0 2))
		 (equal (aref2 :fake-name (m-trans m) 2 1)
			(aref2 :fake-name m 1 2))
		 (equal (aref2 :fake-name (m-trans m) 2 2)
			(aref2 :fake-name m 2 2)))))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-1-lemma1
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (+ (* s s) (* c c)) 1)
		 (equal (+ (* x x) (* z z)) 1))
	    (equal (- (* c
			 (+ c (* z z (- 1 c))))
		      (* (* x s)
			 (- (* x s))))
		   (+ c (* x x (- 1 c)))))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-lemma2
			     (a (* c c)) (c (* z z)))
		  (:instance r3-rotationp-r-theta-11-1-lemma3 (c (* c c)) (a (* x x)) (b (* s s)))
		  (:instance r3-rotationp-r-theta-11-1-lemma1 (s x) (c z)))
	    ))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-1-lemma2
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 1)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-y1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 2)
			(- (* (point-in-r3-y1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-x1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 1)
			(+ (* (point-in-r3-z1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-x1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 2)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  0 0)
		   (- (* (acl2-cosine angle)
			 (+ (acl2-cosine angle) (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))
		      (* (* (point-in-r3-x1 p) (acl2-sine angle))
			 (- (* (point-in-r3-x1 p) (acl2-sine angle)))))))
   :hints (("goal"
	    :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  )
	    :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
			    )))
   ))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-1
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  0 0)
		   (aref2 :fake-name
			  (rotation-3d angle p)
			  0 0)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-1-lemma1
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  (:instance r3-rotationp-r-theta-8 (angle angle))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-1-lemma2 (angle angle) (p p))
		  )
	    :in-theory nil
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-2-lemma1
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (+ (* s s) (* c c)) 1)
		 (equal (+ (* x x) (* z z)) 1))
	    (equal (- (* (* (* x z) (- 1 c))
			 (* x s))
		      (* (+ c (* z z (- 1 c)))
			 (- (* z s))))
		   (* z s)))))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-2-lemma2
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 1)
			(- (* (point-in-r3-x1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-z1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 2)
			(+ (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-y1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 1)
			(+ (* (point-in-r3-z1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-x1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 2)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  0 1)
		   (- (* (* (* (point-in-r3-x1 p) (point-in-r3-z1 p)) (- 1 (acl2-cosine angle)))
			 (* (point-in-r3-x1 p) (acl2-sine angle)))
		      (* (+ (acl2-cosine angle) (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))
			 (- (* (point-in-r3-z1 p) (acl2-sine angle)))))))
   :hints (("goal"
	    :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  )
	    :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
			    )))
   ))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-2
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  0 1)
		   (aref2 :fake-name
			  (rotation-3d angle p)
			  1 0)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-2-lemma1
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  (:instance r3-rotationp-r-theta-8 (angle angle))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-2-lemma2 (angle angle) (p p))
		  )
	    :in-theory nil
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-3-lemma1
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (+ (* s s) (* c c)) 1)
		 (equal (+ (* x x) (* z z)) 1))
	    (equal (- (* (- (* z s))
			 (- (* x s)))
		      (* c (* x z (- 1 c))))
		   (* z x (- 1 c))))))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-3-lemma2
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 1)
			(- (* (point-in-r3-x1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-z1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 2)
			(+ (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-y1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 1)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-y1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 2)
			(- (* (point-in-r3-y1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-x1 p) (acl2-sine angle)))))

	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  0 2)
		   (- (* (- (* (point-in-r3-z1 p) (acl2-sine angle)))
			 (- (* (point-in-r3-x1 p) (acl2-sine angle))))
		      (* (acl2-cosine angle) (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))))
   :hints (("goal"
	    :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  )
	    :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
			    )))
   ))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-3
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  0 2)
		   (aref2 :fake-name
			  (rotation-3d angle p)
			  2 0)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-3-lemma1
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  (:instance r3-rotationp-r-theta-8 (angle angle))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-3-lemma2 (angle angle) (p p))
		  )
	    :in-theory nil
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-4-lemma1
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (+ (* s s) (* c c)) 1)
		 (equal (+ (* x x) (* z z)) 1))
	    (equal (- (* (- (* x s))
			 (* z x (- 1 c)))
		      (* (+ c (* z z (- 1 c)))
			 (* z s)))
		   (- (* z s))))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-4-lemma2
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 0)
			(+ (* (point-in-r3-y1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-z1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 2)
			(- (* (point-in-r3-y1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-x1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 0)
			(- (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-y1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 2)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))))

	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  1 0)
		   (- (* (- (* (point-in-r3-x1 p) (acl2-sine angle)))
			 (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle))))
		      (* (+ (acl2-cosine angle) (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle))))
			 (* (point-in-r3-z1 p) (acl2-sine angle))))))
   :hints (("goal"
	    :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  )
	    :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
			    )))
   ))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-4
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  1 0)
		   (aref2 :fake-name
			  (rotation-3d angle p)
			  0 1)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-4-lemma1
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  (:instance r3-rotationp-r-theta-8 (angle angle))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-4-lemma2 (angle angle) (p p))
		  )
	    :in-theory nil
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-5-lemma1
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (+ (* s s) (* c c)) 1)
		 (equal (+ (* x x) (* z z)) 1))
	    (equal (- (* (+ c (* x x (- 1 c)))
			 (+ c (* z z (- 1 c))))
		      (* (* z x (- 1 c))
			 (* x z (- 1 c))))
		   c))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-5-lemma2
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 0)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 2)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 2)
			(+ (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-y1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 0)
			(- (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-y1 p) (acl2-sine angle)))))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  1 1)
		   (- (* (+ (acl2-cosine angle) (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle))))
			 (+ (acl2-cosine angle) (* (point-in-r3-z1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))
		      (* (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
			 (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))))))
   :hints (("goal"
	    :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  )
	    :in-theory (e/d () (point-in-r3 r3-matrixp point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=)
			    )))
   ))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-5
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  1 1)
		   (aref2 :fake-name
			  (rotation-3d angle p)
			  1 1)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-5-lemma1
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  (:instance r3-rotationp-r-theta-8 (angle angle))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-5-lemma2 (angle angle) (p p))
		  )
	    :in-theory nil
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-6-lemma1
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (+ (* s s) (* c c)) 1)
		 (equal (+ (* x x) (* z z)) 1))
	    (equal (- (* (* x z (- 1 c)) (* z s))
		      (* (- (* x s)) (+ c (* x x (- 1 c)))))
		   (* x s)))))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-6-lemma2
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 0)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 2)
			(+ (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-y1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 0)
			(+ (* (point-in-r3-y1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-z1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 2)
			(- (* (point-in-r3-y1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-x1 p) (acl2-sine angle)))))

	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  1 2)
		   (- (* (* (point-in-r3-x1 p) (point-in-r3-z1 p) (- 1 (acl2-cosine angle)))
			 (* (point-in-r3-z1 p) (acl2-sine angle)))
		      (* (- (* (point-in-r3-x1 p) (acl2-sine angle)))
			 (+ (acl2-cosine angle) (* (point-in-r3-x1 p)
						   (point-in-r3-x1 p)
						   (- 1 (acl2-cosine angle))))))
		   ))
   :hints (("goal"
	    :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  )
	    :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
	    )
	   ))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-6
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  1 2)
		   (aref2 :fake-name
			  (rotation-3d angle p)
			  2 1)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-6-lemma1
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  (:instance r3-rotationp-r-theta-8 (angle angle))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-6-lemma2 (angle angle) (p p))
		  )
	    :in-theory nil
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-7-lemma1
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (+ (* s s) (* c c)) 1)
		 (equal (+ (* x x) (* z z)) 1))
	    (equal (- (* (* z s) (* x s))
		      (* (* z x) (- 1 c) c))
		   (* x z (- 1 c))))))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-7-lemma2
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 0)
			(+ (* (point-in-r3-y1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-z1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 1 1)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-y1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 0)
			(- (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-y1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 1)
			(+ (* (point-in-r3-z1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-x1 p) (acl2-sine angle)))))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  2 0)
		   (- (* (* (point-in-r3-z1 p) (acl2-sine angle))
			 (* (point-in-r3-x1 p) (acl2-sine angle)))
		      (* (* (point-in-r3-z1 p) (point-in-r3-x1 p)) (- 1 (acl2-cosine angle))
			 (acl2-cosine angle)))
		   ))
   :hints (("goal"
	    :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  )
	    :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
	    )
	   ))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-7
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  2 0)
		   (aref2 :fake-name
			  (rotation-3d angle p)
			  0 2)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-7-lemma1
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  (:instance r3-rotationp-r-theta-8 (angle angle))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-7-lemma2 (angle angle) (p p))
		  )
	    :in-theory nil
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-8-lemma1
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (+ (* s s) (* c c)) 1)
		 (equal (+ (* x x) (* z z)) 1))
	    (equal (- (* (- (* z s)) (* z x) (- 1 c))
		      (* (* x s) (+ c (* x x (- 1 c)))))
		   (- (* x s)))))

 (defthmd r3-rotationp-r-theta-11-1-8-lemma3
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c))
	    (equal (- (* (- (* z s)) (* z x) (- 1 c))
		      (* (* x s) (+ c (* x x (- 1 c)))))
		   (+ (- (* z z s x))
		      (* z z s x c)
		      (- (* x s c))
		      (- (* x x x s))
		      (* x x x s c)))))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-8-lemma2
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 0)
			(+ (acl2-cosine angle)
			   (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 1)
			(+ (* (point-in-r3-z1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-x1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 2 0)
			(- (* (point-in-r3-z1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-y1 p) (acl2-sine angle))))
		 (equal (aref2 :fake-name (rotation-3d angle p) 0 1)
			(- (* (point-in-r3-x1 p) (point-in-r3-y1 p) (- 1 (acl2-cosine angle)))
			   (* (point-in-r3-z1 p) (acl2-sine angle)))))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  2 1)
		   (+ (- (* (point-in-r3-z1 p) (point-in-r3-z1 p) (acl2-sine angle) (point-in-r3-x1 p)))
		      (* (point-in-r3-z1 p) (point-in-r3-z1 p) (acl2-sine angle) (point-in-r3-x1 p)
			 (acl2-cosine angle))
		      (- (* (point-in-r3-x1 p) (acl2-sine angle) (acl2-cosine angle)))
		      (- (* (point-in-r3-x1 p) (point-in-r3-x1 p) (point-in-r3-x1 p) (acl2-sine angle)))
		      (* (point-in-r3-x1 p) (point-in-r3-x1 p) (point-in-r3-x1 p) (acl2-sine angle)
			 (acl2-cosine angle)))
		   ))
   :hints (("goal"
	    :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  )
	    :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
	    )
	   ))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-8
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  2 1)
		   (aref2 :fake-name
			  (rotation-3d angle p)
			  1 2)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-8-lemma1
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance r3-rotationp-r-theta-11-1-8-lemma3
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  (:instance r3-rotationp-r-theta-8 (angle angle))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-8-lemma2 (angle angle) (p p))
		  )
	    :in-theory nil
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-9-lemma1
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (* s s) (- 1 (* c c)))
		 (equal (* x x) (- 1 (* z z))))
	    (equal (- (* (+ c (* x x (- 1 c))) c)
		      (* (* z s) (- (* z s))))
		   (+ (* c x x) (* z z))))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-lemma2 (a (* c c)) (c (* x x)))
		  (:instance r3-rotationp-r-theta-11-1-lemma3 (a (* z z)) (b (* c c)) (c (* s s)))
		  (:instance r3-rotationp-r-theta-11-1-lemma1 (s s) (c c))
		  (:instance r3-rotationp-r-theta-11-1-lemma1 (s z) (c x))
		  ))
	   ("subgoal 1"
	    :use((:instance r3-rotationp-r-theta-11-1-lemma2 (a (* c c)) (c (* x x)))
		 (:instance r3-rotationp-r-theta-11-1-lemma3 (a (* z z)) (b (* c c)) (c (* s s)))
		 (:instance r3-rotationp-r-theta-11-1-lemma1 (s s) (c c))
		 (:instance r3-rotationp-r-theta-11-1-lemma1 (s z) (c x)))
	    )))

 (defthmd r3-rotationp-r-theta-11-1-9-lemma2
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp c)
		 (equal (+ (* s s) (* c c)) 1)
		 (equal (+ (* x x) (* z z)) 1))
	    (equal (- (* (+ c (* x x (- 1 c))) c)
		      (* (* z s) (- (* z s))))
		   (+ c (* z z) (- (* z z c)))))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-9-lemma1)
		  (:instance r3-rotationp-r-theta-11-1-lemma1 (s x) (c z)))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11-1-9-lemma3
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  2 2)
		   (- (* (+ (acl2-cosine angle) (* (point-in-r3-x1 p) (point-in-r3-x1 p) (- 1 (acl2-cosine angle)))) (acl2-cosine angle))
		      (* (* (point-in-r3-z1 p) (acl2-sine angle)) (- (* (point-in-r3-z1 p) (acl2-sine angle)))))))
   :hints (("goal"
	    :use ((:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  )
	    :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
	    )))

 (defthmd r3-rotationp-r-theta-11-1-9
   (implies (and (realp angle)
		 (point-in-r3 p)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (equal (aref2 :fake-name
			  (r3-m-inverse (rotation-3d angle p))
			  2 2)
		   (aref2 :fake-name
			  (rotation-3d angle p)
			  2 2)))
   :hints (("goal"
	    :use ((:instance r3-rotationp-r-theta-11-1-9-lemma2
			     (x (point-in-r3-x1 p))
			     (z (point-in-r3-z1 p))
			     (s (acl2-sine angle))
			     (c (acl2-cosine angle)))
		  (:instance sin**2+cos**2 (x angle))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1-lemma4 (p p))
		  (:instance r3-rotationp-r-theta-8 (angle angle))
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-rotationp-r-theta-11-1-9-lemma3 (angle angle) (p p))
		  )
	    :in-theory (e/d () (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
	    )))
 )

(defthmd r3-rotationp-r-theta-11-1
  (implies (and (realp angle)
                (equal (r3-m-determinant (rotation-3d angle p)) 1)
                (point-in-r3 p)
                (equal (point-in-r3-y1 p) 0)
                (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1))
           (and (equal (aref2 :fake-name
                              (r3-m-inverse (rotation-3d angle p))
                              2 2)
                       (aref2 :fake-name
                              (rotation-3d angle p)
                              2 2))
                (equal (aref2 :fake-name
                              (r3-m-inverse (rotation-3d angle p))
                              2 1)
                       (aref2 :fake-name
                              (rotation-3d angle p)
                              1 2))
                (equal (aref2 :fake-name
                              (r3-m-inverse (rotation-3d angle p))
                              2 0)
                       (aref2 :fake-name
                              (rotation-3d angle p)
                              0 2))
                (equal (aref2 :fake-name
                              (r3-m-inverse (rotation-3d angle p))
                              1 2)
                       (aref2 :fake-name
                              (rotation-3d angle p)
                              2 1))
                (equal (aref2 :fake-name
                              (r3-m-inverse (rotation-3d angle p))
                              1 1)
                       (aref2 :fake-name
                              (rotation-3d angle p)
                              1 1))
                (equal (aref2 :fake-name
                              (r3-m-inverse (rotation-3d angle p))
                              1 0)
                       (aref2 :fake-name
                              (rotation-3d angle p)
                              0 1))
                (equal (aref2 :fake-name
                              (r3-m-inverse (rotation-3d angle p))
                              0 2)
                       (aref2 :fake-name
                              (rotation-3d angle p)
                              2 0))
                (equal (aref2 :fake-name
                              (r3-m-inverse (rotation-3d angle p))
                              0 1)
                       (aref2 :fake-name
                              (rotation-3d angle p)
                              1 0))
                (equal (aref2 :fake-name
                              (r3-m-inverse (rotation-3d angle p))
                              0 0)
                       (aref2 :fake-name
                              (rotation-3d angle p)
                              0 0))
                ))
  :hints (("goal"
           :use ((:instance r3-rotationp-r-theta-11-1-9)
                 (:instance r3-rotationp-r-theta-11-1-8)
                 (:instance r3-rotationp-r-theta-11-1-7)
                 (:instance r3-rotationp-r-theta-11-1-6)
                 (:instance r3-rotationp-r-theta-11-1-5)
                 (:instance r3-rotationp-r-theta-11-1-4)
                 (:instance r3-rotationp-r-theta-11-1-3)
                 (:instance r3-rotationp-r-theta-11-1-2)
                 (:instance r3-rotationp-r-theta-11-1-1)
                 )
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r3-rotationp-r-theta-11
   (implies (and (realp angle)
		 (equal (r3-m-determinant (rotation-3d angle p)) 1)
		 (point-in-r3 p)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1))
	    (m-= (r3-m-inverse (rotation-3d angle p))
		 (m-trans (rotation-3d angle p))))
   :hints (("goal"
	    :use ((:instance sin**2+cos**2 (x angle))
		  (:instance r3-rotationp-r-theta-8)
		  (:instance rotation-about-witness-values (angle angle) (point p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p p))
		  (:instance r3-matrixp-r3-m-inverse (m (rotation-3d angle p)))
		  (:instance r3-matrixp-m-trans (m (rotation-3d angle p)))
		  (:instance r3-m-inverse-= (m (rotation-3d angle p)))
		  (:instance m-trans-values (m (rotation-3d angle p)))
		  (:instance r3-rotationp-r-theta-11-1)
		  )
	    :in-theory (e/d (m-= header dimensions alist2p) (point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 m-trans rotation-3d r3-m-determinant point-on-s2-not-d acl2-sqrt sin**2+cos**2 acl2-sqrt r3-m-inverse aref2 aref2-m-trans r3-m-inverse-=))
	    )))
 )

(defthmd r3-rotationp-r-theta
  (implies (realp angle)
           (r3-rotationp (rotation-3d angle (point-on-s2-not-d))))
  :hints (("goal"
           :use ((:instance r3-rotationp-r-theta-11 (angle angle) (p (point-on-s2-not-d)))
                 (:instance r3-rotationp-r-theta-10 (angle angle) (p (point-on-s2-not-d)))
                 (:instance r3-rotationp-r-theta-2 (point (point-on-s2-not-d)))
                 (:instance r3-rotationp-r-theta-5 (point (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance r3-rotationp (m (rotation-3d angle (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta-1 (angle angle)))
           :in-theory nil
           )))

(defthmd r-theta-0=id
  (implies (point-in-r3 u)
           (m-= (rotation-3d 0 u)
                (id-rotation)))
  :hints (("goal"
           :in-theory (enable m-= aref2 dimensions header)
           )))

(defthmd r-theta*p=p=>r--theta*p=p-1
  (implies (m-= m1 m2)
           (m-= (m-* m3 m1) (m-* m3 m2))))

(defthmd r-theta*p=p=>r--theta*p=p-2
  (implies (m-= (m-* m1 m2 m3) (m-* m4 m5))
           (m-= (m-* (m-* m1 m2) m3) (m-* m4 m5))))

(defthmd r-theta*p=p=>r--theta*p=p
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (realp angle)
                (m-= (m-* (rotation-3d angle u) p) p))
           (m-= (m-* (rotation-3d (- angle) u) p) p))
  :hints (("goal"
           :use ((:instance r-theta*p=p=>r--theta*p=p-1
                            (m1 (m-* (rotation-3d angle u) p))
                            (m2 p)
                            (m3 (rotation-3d (- angle) u)))
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (- angle))
                            (angle2 angle)
                            (u u))
                 (:instance r-theta-0=id (u u))
                 (:instance m-*point-id=point (p1 p))
                 (:instance r-theta*p=p=>r--theta*p=p-2
                            (m1 (rotation-3d (- angle) u))
                            (m2 (rotation-3d angle u))
                            (m3 p)
                            (m4 (rotation-3d (- angle) u))
                            (m5 p))
                 )
           :in-theory (e/d () (associativity-of-m-* m-* aref2 rotation-3d point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 id-rotation point-in-r3 (:executable-counterpart id-rotation)))
           )))

(defthmd m-=p1p2-implies
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= p1 p2))
           (and (equal (aref2 :fake-name p1 0 0)
                       (aref2 :fake-name p2 0 0))
                (equal (aref2 :fake-name p1 1 0)
                       (aref2 :fake-name p2 1 0))
                (equal (aref2 :fake-name p1 2 0)
                       (aref2 :fake-name p2 2 0))))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd r-theta*p=p-lemma1-1
  (implies (and (r3-matrixp m)
                (point-in-r3 p))
           (point-in-r3 (m-* m p))))

(defthmd r-theta*p=p-lemma1-2
  (implies (and (point-in-r3 u)
                (realp angle))
           (and (alist2p :fake-name (rotation-3d angle u))
                (alist2p :fake-name (rotation-3d (- angle) u))))
  :hints (("goal"
           :in-theory (enable alist2p)
           )))

(defthmd r-theta*p=p-lemma1-3
  (implies (and (point-in-r3 u)
                (point-in-r3 p)
                (realp angle))
           (equal (cadr (dimensions :fake-name (rotation-3d angle u)))
                  (car (dimensions :fake-name p))))
  :hints (("goal"
           :in-theory (e/d (header dimensions) ())
           )))

(defthmd r-theta*p=p-lemma1-4
  (implies (and (point-in-r3 u)
                (point-in-r3 p)
                (realp angle))
           (equal (aref2 :fake-name (m-* (rotation-3d angle u) p) 0 0)
                  (+ (* (+ (acl2-cosine angle)
                           (* (point-in-r3-x1 u) (point-in-r3-x1 u) (- 1 (acl2-cosine angle))))
                        (point-in-r3-x1 p))
                     (* (- (* (point-in-r3-x1 u) (point-in-r3-y1 u) (- 1 (acl2-cosine angle)))
                           (* (point-in-r3-z1 u) (acl2-sine angle)))
                        (point-in-r3-y1 p))
                     (* (+ (* (point-in-r3-x1 u) (point-in-r3-z1 u) (- 1 (acl2-cosine angle)))
                           (* (point-in-r3-y1 u) (acl2-sine angle)))
                        (point-in-r3-z1 p)))))
  :hints (("goal"
           :use ((:instance aref2-m-*
                            (m1 (rotation-3d angle u))
                            (m2 p)
                            (name :fake-name)
                            (i 0)
                            (j 0))
                 (:instance rotation-about-witness-values (angle angle) (point u))
                 (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                 )
           :in-theory (e/d (header dimensions) ())
           )))

(defthmd r-theta*p=p-lemma1-5
  (implies (and (point-in-r3 u)
                (point-in-r3 p)
                (realp angle))
           (equal (aref2 :fake-name (m-* (rotation-3d angle u) p) 2 0)
                  (+ (* (- (* (point-in-r3-z1 u) (point-in-r3-x1 u) (- 1 (acl2-cosine angle)))
                           (* (point-in-r3-y1 u) (acl2-sine angle)))
                        (point-in-r3-x1 p))
                     (* (+ (* (point-in-r3-z1 u) (point-in-r3-y1 u) (- 1 (acl2-cosine angle)))
                           (* (point-in-r3-x1 u) (acl2-sine angle)))
                        (point-in-r3-y1 p))
                     (* (+ (acl2-cosine angle)
                           (* (point-in-r3-z1 u) (point-in-r3-z1 u) (- 1 (acl2-cosine angle))))
                        (point-in-r3-z1 p)))))
  :hints (("goal"
           :use ((:instance aref2-m-*
                            (m1 (rotation-3d angle u))
                            (m2 p)
                            (name :fake-name)
                            (i 2)
                            (j 0))
                 (:instance rotation-about-witness-values (angle angle) (point u))
                 (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
                 )
           :in-theory (e/d (header dimensions) ())
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r-theta*p=p-lemma1
   (implies (and (point-in-r3 p)
		 (point-in-r3 u)
		 (equal (point-in-r3-y1 u) 0)
		 (realp angle)
		 (m-= (m-* (rotation-3d angle u) p)
		      (m-* (rotation-3d (- angle) u) p)))
	    (and (equal (* (point-in-r3-z1 u) (acl2-sine angle) (point-in-r3-y1 p)) 0)
		 (equal (* (point-in-r3-x1 u) (acl2-sine angle) (point-in-r3-y1 p)) 0)))
   :hints (("goal"
	    :use ((:instance m-=p1p2-implies
			     (p1 (m-* (rotation-3d angle u) p))
			     (p2 (m-* (rotation-3d (- angle) u) p)))
		  (:instance r-theta*p=p-lemma1-4 (u u) (p p) (angle angle))
		  (:instance r-theta*p=p-lemma1-4 (u u) (p p) (angle (- angle)))
		  (:instance r-theta*p=p-lemma1-5 (u u) (p p) (angle angle))
		  (:instance r-theta*p=p-lemma1-5 (u u) (p p) (angle (- angle)))
		  (:instance r-theta*p=p-lemma1-1 (m (rotation-3d angle u)) (p p))
		  (:instance r-theta*p=p-lemma1-1 (m (rotation-3d (- angle) u)) (p p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
		  (:instance r3-rotationp-r-theta-10 (angle (- angle)) (p u))
		  (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
		  (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
		  )
	    :in-theory (e/d () (m-= alist2p array2p m-* rotation-3d aref2-m-* aref2))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r-theta*p=p-lemma2-1
   (implies (and (point-in-r3 u)
		 (point-in-r3 p)
		 (realp angle))
	    (equal (aref2 :fake-name (m-* (rotation-3d angle u) p) 1 0)
		   (+ (* (+ (* (point-in-r3-y1 u) (point-in-r3-x1 u) (- 1 (acl2-cosine angle)))
			    (* (point-in-r3-z1 u) (acl2-sine angle)))
			 (point-in-r3-x1 p))
		      (* (+ (acl2-cosine angle)
			    (* (point-in-r3-y1 u) (point-in-r3-y1 u) (- 1 (acl2-cosine angle))))
			 (point-in-r3-y1 p))
		      (* (- (* (point-in-r3-y1 u) (point-in-r3-z1 u) (- 1 (acl2-cosine angle)))
			    (* (point-in-r3-x1 u) (acl2-sine angle)))
			 (point-in-r3-z1 p)))))
   :hints (("goal"
	    :use ((:instance aref2-m-*
			     (m1 (rotation-3d angle u))
			     (m2 p)
			     (name :fake-name)
			     (i 1)
			     (j 0))
		  (:instance rotation-about-witness-values (angle angle) (point u))
		  (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
		  )
	    :in-theory (e/d (header dimensions) ())
	    )))

 (defthmd r-theta*p=p-lemma2
   (implies (and (point-in-r3 p)
		 (point-in-r3 u)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (point-in-r3-y1 u) 0)
		 (realp angle)
		 (m-= (m-* (rotation-3d angle u) p) p))
	    (equal (- (* (point-in-r3-z1 u) (acl2-sine angle) (point-in-r3-x1 p))
		      (* (point-in-r3-x1 u) (acl2-sine angle) (point-in-r3-z1 p)))
		   0))
   :hints (("goal"
	    :use ((:instance m-=p1p2-implies
			     (p1 (m-* (rotation-3d angle u) p))
			     (p2 p))
		  (:instance r-theta*p=p-lemma2-1 (u u) (p p) (angle angle))
		  (:instance r-theta*p=p-lemma1-1 (m (rotation-3d angle u)) (p p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
		  (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
		  (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
		  )
	    :in-theory (e/d () (m-= alist2p array2p m-* rotation-3d aref2-m-* aref2))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd sine-p2=0-lemma-4-2
   (implies (and (realp p)
		 (realp q)
		 (realp r)
		 (equal (* p q) r)
		 (not (equal q 0)))
	    (equal (/ r q) p)))

 (defthmd sine-p2=0-lemma-4-1
   (implies (and (not (equal x 0))
		 (realp x)
		 (realp z)
		 (realp p1)
		 (realp p3)
		 (equal (* p1 z) (* p3 x)))
	    (equal (/ (* p1 z) x) p3))
   :hints (("goal"
	    :use ((:instance sine-p2=0-lemma-4-2 (r (* p1 z)) (p p3) (q x)))
	    )))

 (defthmd sine-p2=0-lemma-4-3-1
   (implies (equal x y)
	    (equal (* x z) (* y z))))

 (defthmd sine-p2=0-lemma-4-3
   (implies (and (not (equal x 0))
		 (equal (* p1 (/ x) z) p3)
		 (realp x)
		 (realp z)
		 (realp p1)
		 (realp p3)
		 (equal (+ (expt x 2) (expt z 2)) 1)
		 (equal (+ (expt p1 2) (expt p3 2)) 1)
		 (equal (* p1 z) (* p3 x)))
	    (equal (+ (* p1 p1 x x) (* p1 p1 z z)) (* x x)))
   :hints (("subgoal 1"
	    :use ((:instance sine-p2=0-lemma-4-3-1
			     (x (+ (expt p1 2)
				   (* (expt p1 2) (expt z 2) (expt x -2))))
			     (y 1)
			     (z (expt x 2))))
	    )
	   ))

 (defthmd sine-p2=0-lemma-4-4
   (equal (+ (* (expt p1 2) (expt x 2))
	     (* (expt p1 2) (expt z 2)))
	  (* p1 p1 (+ (* x x) (* z z)))))

 (defthm sine-p2=0-lemma-4-5
   (implies (and (realp x)
		 (realp p1)
		 (equal (expt p1 2) (expt x 2)))
	    (or (equal p1 x)
		(equal p1 (- x))))
   :hints (("goal"
	    :use ((:instance sqrt-*-x-x (x x))
		  (:instance sqrt-*-x-x (x p1)))
	    :in-theory (disable sqrt-*-x-x y-=-sqrt sqrt-=-y)
	    ))
   :rule-classes nil)
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd sine-p2=0-lemma
   (implies (and (realp x)
		 (realp z)
		 (equal (+ (* x x) (* z z)) 1)
		 (realp s)
		 (realp p2)
		 (equal (* z s p2) 0)
		 (equal (* x s p2) 0))
	    (equal (* s p2) 0)))

 (defthm sine-p2=0-lemma-1
   (implies (and (realp x)
		 (realp z)
		 (equal (+ (* x x) (* z z)) 1)
		 (realp s)
		 (realp p2)
		 (equal (* z s p2) 0)
		 (equal (* x s p2) 0))
	    (or (equal s 0)
		(equal p2 0)))
   :rule-classes nil
   )

 (defthm sine-p2=0-lemma-2
   (implies (and (realp x)
		 (realp z)
		 (realp s)
		 (realp p1)
		 (realp p3)
		 (equal (- (* z s p1)
			   (* x s p3))
			0))
	    (or (equal s 0)
		(equal (* z p1) (* x p3))))
   :rule-classes nil
   )

 (defthm sine-p2=0-lemma-3
   (implies (and (realp x)
		 (realp y)
		 (realp z)
		 (realp p1)
		 (realp p2)
		 (realp p3)
		 (equal y 0)
		 (equal p2 0)
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* p1 p1) (* p2 p2) (* p3 p3)) 1)
		 (equal (* z p1) (* x p3))
		 (equal x 0))
	    (and (or (equal p3 z)
		     (equal p3 (- z)))
		 (equal p1 0)))
   :rule-classes nil)

 (defthm sine-p2=0-lemma-4
   (implies (and (realp x)
		 (realp y)
		 (realp z)
		 (realp p1)
		 (realp p2)
		 (realp p3)
		 (equal p2 0)
		 (equal y 0)
		 (equal (+ (* x x) (* y y) (* z z)) 1)
		 (equal (+ (* p1 p1) (* p2 p2) (* p3 p3)) 1)
		 (equal (* z p1) (* x p3)))
	    (or (and (equal p1 x)
		     (equal p3 z))
		(and (equal p1 (- x))
		     (equal p3 (- z)))))
   :hints (("goal"
	    :use ((:instance sine-p2=0-lemma-3 (x x) (y y) (z z) (p1 p1) (p2 p2) (p3 p3))
		  (:instance sine-p2=0-lemma-4-1 (x x) (z z) (p1 p1) (p3 p3))
		  (:instance sine-p2=0-lemma-4-3 (x x) (z z) (p1 p1) (p3 p3))
		  (:instance sine-p2=0-lemma-4-4 (p1 p1) (x x) (z z))
		  (:instance sine-p2=0-lemma-4-5)
		  )
	    ))
   :rule-classes nil)
 )

(defthmd r-theta*p=p=>sine=0
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (realp angle)
                (or (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-y1 p)
                                (point-in-r3-y1 u)))
                    (not (equal (point-in-r3-z1 p)
                                (point-in-r3-z1 u))))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-y1 p)
                                (- (point-in-r3-y1 u))))
                    (not (equal (point-in-r3-z1 p)
                                (- (point-in-r3-z1 u)))))
                (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (equal (point-in-r3-y1 u) 0)
                (m-= (m-* (rotation-3d angle u) p) p))
           (equal (acl2-sine angle) 0))
  :hints (("goal"
           :use ((:instance r-theta*p=p=>r--theta*p=p (p p) (u u) (angle angle))
                 (:instance r-theta*p=p-lemma1 (p p) (u u) (angle angle))
                 (:instance r-theta*p=p-lemma2 (p p) (u u) (angle angle))
                 (:instance sine-p2=0-lemma
                            (x (point-in-r3-x1 u))
                            (z (point-in-r3-z1 u))
                            (s (acl2-sine angle))
                            (p2 (point-in-r3-y1 p)))
                 (:instance sine-p2=0-lemma-1
                            (x (point-in-r3-x1 u))
                            (z (point-in-r3-z1 u))
                            (s (acl2-sine angle))
                            (p2 (point-in-r3-y1 p)))
                 (:instance sine-p2=0-lemma-2
                            (x (point-in-r3-x1 u))
                            (z (point-in-r3-z1 u))
                            (s (acl2-sine angle))
                            (p1 (point-in-r3-x1 p))
                            (p3 (point-in-r3-z1 p)))
                 (:instance sine-p2=0-lemma-4
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (p1 (point-in-r3-x1 p))
                            (p2 (point-in-r3-y1 p))
                            (p3 (point-in-r3-z1 p)))
                 )
           :in-theory (disable aref2 m-= m-* r3-rotationp rotation-3d r3-matrixp)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd r-theta*p=p=>cosine=1-lemma1
   (implies (and (point-in-r3 p)
		 (point-in-r3 u)
		 (realp angle)
		 (equal (point-in-r3-y1 u) 0)
		 (m-= (m-* (rotation-3d angle u) p) p)
		 (equal (acl2-sine angle) 0))
	    (or (equal (acl2-cosine angle) 1)
		(equal (point-in-r3-y1 p) 0)))
   :hints (("goal"
	    :use ((:instance m-=p1p2-implies
			     (p1 (m-* (rotation-3d angle u) p))
			     (p2 p))
		  (:instance r-theta*p=p-lemma2-1 (u u) (p p) (angle angle))
		  (:instance r-theta*p=p-lemma1-1 (m (rotation-3d angle u)) (p p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
		  (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
		  (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
		  )
	    :in-theory (e/d () (m-= alist2p array2p m-* rotation-3d aref2-m-* aref2))
	    )))

 (defthmd r-theta*p=p=>cosine=1-lemma2-1
   (implies (equal (- 1 (* x x)) (* z z))
	    (equal (- (* 2 p1) (* 2 p1 x x))
		   (* 2 p1 z z))))

 (defthmd r-theta*p=p=>cosine=1-lemma2-2
   (implies (and (realp p1)
		 (realp p3)
		 (realp x)
		 (realp z)
		 (equal (+ (* x x) (* z z)) 1)
		 (equal (- (* 2 p1) (* 2 p1 x x))
			(* 2 x p3 z)))
	    (equal (* p1 z z) (* x p3 z)))
   :hints (("goal"
	    :use ((:instance r-theta*p=p=>cosine=1-lemma2-1 (p1 p1) (x x)))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r-theta*p=p=>cosine=1-lemma2
   (implies (and (point-in-r3 p)
		 (point-in-r3 u)
		 (realp angle)
		 (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
			   (* (point-in-r3-y1 u) (point-in-r3-y1 u))
			   (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
			1)
		 (equal (point-in-r3-y1 u) 0)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (acl2-cosine angle) -1)
		 (m-= (m-* (rotation-3d angle u) p) p)
		 (equal (acl2-sine angle) 0))
	    (equal (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-z1 u))
		   (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-z1 u))))
   :hints (("goal"
	    :use ((:instance m-=p1p2-implies
			     (p1 (m-* (rotation-3d angle u) p))
			     (p2 p))
		  (:instance r-theta*p=p-lemma1-4 (u u) (p p) (angle angle))
		  (:instance r-theta*p=p-lemma1-1 (m (rotation-3d angle u)) (p p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
		  (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
		  (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
		  (:instance r-theta*p=p=>cosine=1-lemma2-2
			     (p1 (point-in-r3-x1 p))
			     (p3 (point-in-r3-z1 p))
			     (x (point-in-r3-x1 u))
			     (z (point-in-r3-z1 u)))
		  )
	    :in-theory (e/d () (m-= alist2p array2p m-* rotation-3d aref2-m-* aref2))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r-theta*p=p=>cosine=1-lemma3
   (implies (and (point-in-r3 p)
		 (point-in-r3 u)
		 (realp angle)
		 (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
			   (* (point-in-r3-y1 u) (point-in-r3-y1 u))
			   (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
			1)
		 (equal (point-in-r3-y1 u) 0)
		 (equal (point-in-r3-y1 p) 0)
		 (equal (acl2-cosine angle) -1)
		 (m-= (m-* (rotation-3d angle u) p) p)
		 (equal (acl2-sine angle) 0))
	    (equal (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-x1 u))
		   (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-x1 u))))
   :hints (("goal"
	    :use ((:instance m-=p1p2-implies
			     (p1 (m-* (rotation-3d angle u) p))
			     (p2 p))
		  (:instance r-theta*p=p-lemma1-5 (u u) (p p) (angle angle))
		  (:instance r-theta*p=p-lemma1-1 (m (rotation-3d angle u)) (p p))
		  (:instance r3-rotationp-r-theta-10 (angle angle) (p u))
		  (:instance r-theta*p=p-lemma1-2 (angle angle) (u u))
		  (:instance r-theta*p=p-lemma1-3 (u u) (p p) (angle angle))
		  (:instance r-theta*p=p=>cosine=1-lemma2-2
			     (p3 (point-in-r3-x1 p))
			     (p1 (point-in-r3-z1 p))
			     (z (point-in-r3-x1 u))
			     (x (point-in-r3-z1 u)))
		  )
	    :in-theory (e/d () (m-= alist2p array2p m-* rotation-3d aref2-m-* aref2))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r-theta*p=p=>cosine=1-lemma4
   (implies (and (point-in-r3 p)
		 (point-in-r3 u)
		 (realp angle)
		 (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
			   (* (point-in-r3-y1 u) (point-in-r3-y1 u))
			   (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
			1)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-y1 p) (point-in-r3-y1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1)
		 (or (not (equal (point-in-r3-x1 p)
				 (point-in-r3-x1 u)))
		     (not (equal (point-in-r3-y1 p)
				 (point-in-r3-y1 u)))
		     (not (equal (point-in-r3-z1 p)
				 (point-in-r3-z1 u))))
		 (or (not (equal (point-in-r3-x1 p)
				 (- (point-in-r3-x1 u))))
		     (not (equal (point-in-r3-y1 p)
				 (- (point-in-r3-y1 u))))
		     (not (equal (point-in-r3-z1 p)
				 (- (point-in-r3-z1 u)))))
		 (equal (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-z1 u))
			(* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-z1 u)))
		 (equal (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-x1 u))
			(* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-x1 u)))
		 (equal (point-in-r3-y1 u) 0)
		 (equal (point-in-r3-y1 p) 0))
	    (and (not (equal (point-in-r3-z1 u) 0))
		 (not (equal (point-in-r3-x1 u) 0))))
   :hints (("goal"
	    :use ((:instance sine-p2=0-lemma-4-5
			     (x (point-in-r3-x1 u))
			     (p1 (point-in-r3-x1 p)))
		  (:instance sine-p2=0-lemma-4-5
			     (x (point-in-r3-z1 u))
			     (p1 (point-in-r3-z1 p)))
		  )
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r-theta*p=p=>cosine=1-lemma5
   (implies (and (point-in-r3 p)
		 (point-in-r3 u)
		 (realp angle)
		 (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
			   (* (point-in-r3-y1 u) (point-in-r3-y1 u))
			   (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
			1)
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-y1 p) (point-in-r3-y1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1)
		 (or (not (equal (point-in-r3-x1 p)
				 (point-in-r3-x1 u)))
		     (not (equal (point-in-r3-y1 p)
				 (point-in-r3-y1 u)))
		     (not (equal (point-in-r3-z1 p)
				 (point-in-r3-z1 u))))
		 (or (not (equal (point-in-r3-x1 p)
				 (- (point-in-r3-x1 u))))
		     (not (equal (point-in-r3-y1 p)
				 (- (point-in-r3-y1 u))))
		     (not (equal (point-in-r3-z1 p)
				 (- (point-in-r3-z1 u)))))
		 (equal (* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-z1 u))
			(* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-z1 u)))
		 (equal (* (point-in-r3-z1 p) (point-in-r3-x1 u) (point-in-r3-x1 u))
			(* (point-in-r3-x1 p) (point-in-r3-z1 u) (point-in-r3-x1 u)))
		 (equal (point-in-r3-y1 u) 0)
		 (equal (point-in-r3-y1 p) 0))
	    (equal (* (point-in-r3-z1 u) (point-in-r3-x1 p))
		   (* (point-in-r3-x1 u) (point-in-r3-z1 p))))
   :hints (("goal"
	    :use (:instance r-theta*p=p=>cosine=1-lemma4 (p p) (u u))
	    ))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))
 (defthmd r-theta*p=p=>cosine=1-1
   (implies (and (realp angle)
		 (equal (acl2-sine angle) 0))
	    (or (equal (acl2-cosine angle) 1)
		(equal (acl2-cosine angle) -1)))
   :hints (("goal"
	    :use ((:instance sin**2+cos**2 (x angle))
		  (:instance sine-p2=0-lemma-4-5 (p1 (acl2-cosine angle)) (x 1)))
	    :in-theory (disable sin**2+cos**2)
	    )))
 )

(defthmd r-theta*p=p=>cosine=1
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (realp angle)
                (or (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-y1 p)
                                (point-in-r3-y1 u)))
                    (not (equal (point-in-r3-z1 p)
                                (point-in-r3-z1 u))))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-y1 p)
                                (- (point-in-r3-y1 u))))
                    (not (equal (point-in-r3-z1 p)
                                (- (point-in-r3-z1 u)))))
                (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (equal (point-in-r3-y1 u) 0)
                (m-= (m-* (rotation-3d angle u) p) p))
           (equal (acl2-cosine angle) 1))
  :hints (("goal"
           :use ((:instance r-theta*p=p=>sine=0 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma1 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma2 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma3 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-lemma5 (p p) (u u))
                 (:instance r-theta*p=p=>cosine=1-1 (angle angle))
                 (:instance sine-p2=0-lemma-4
                            (x (point-in-r3-x1 u))
                            (y (point-in-r3-y1 u))
                            (z (point-in-r3-z1 u))
                            (p1 (point-in-r3-x1 p))
                            (p2 (point-in-r3-y1 p))
                            (p3 (point-in-r3-z1 p)))
                 )
           :in-theory (disable aref2 m-= m-* r3-rotationp rotation-3d r3-matrixp)
           )))

;;;;sin t = 0, cos t =1 => t=0 if t in [0,2*pi)

(defthmd sine-is-0-in-0<2pi=>x=0orpi-1
  (implies (and (realp x)
                (< 0 x)
                (< x (acl2-pi)))
           (> (acl2-sine x) 0))
  :hints (("goal"
           :use ((:instance sine-positive-in-0-pi/2 (x x))
                 (:instance sine-positive-in-pi/2-pi (x x)))
           )))

(defthmd sine-is-0-in-0<2pi=>x=0orpi-2
  (implies (and (realp x)
                (<= 0 x)
                (< x (acl2-pi))
                (equal (acl2-sine x) 0))
           (equal (* x x) 0))
  :hints (("goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-1 (x x)))
           )))

(defthmd sine-is-0-in-0<2pi=>x=0orpi-3
  (implies (and (realp x)
                (< (acl2-pi) x)
                (< x (* 2 (acl2-pi))))
           (< (acl2-sine x) 0))
  :hints (("goal"
           :use ((:instance sine-negative-in-pi-3pi/2 (x x))
                 (:instance sine-negative-in-3pi/2-2pi (x x)))
           )))

(defthmd sine-is-0-in-0<2pi=>x=0orpi-4
  (implies (and (realp x)
                (<= (acl2-pi) x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (equal (* x x) (* (acl2-pi) (acl2-pi))))
  :hints (("goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-3 (x x)))
           ))
  )

(defthmd sine-is-0-in-0<2pi=>x=0orpi-5
  (implies (and (realp x)
                (<= 0 x)
                (equal (acl2-sine x) 0)
                (< x (* 2 (acl2-pi))))
           (or (equal (* x x) 0)
               (equal (* x x) (* (acl2-pi) (acl2-pi)))))
  :hints (("goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-2)
                 (:instance sine-is-0-in-0<2pi=>x=0orpi-4))
           )))

(encapsulate
 ()

 (local (include-book "nonstd/nsa/inverse-trig" :dir :system))

 (defthmd cosine-is-1-in-0<2pi=>x=0-1
   (implies (and (realp x)
		 (<= 0 x)
		 (equal (acl2-cosine x) 1)
		 (<= x (acl2-pi)))
	    (equal (* x x) 0))
   :hints (("goal"
	    :cases ((equal x 0)
		    (not (equal x 0)))
	    :use ((:instance cosine-positive-in-0-pi/2 (x x))
		  (:instance cosine-pi/2)
		  (:instance cosine-pi)
		  (:instance cosine-negative-in-pi/2-pi (x x)))
	    )
	   ("subgoal 1"
	    :use ((:instance cosine-is-1-1-on-domain (x1 0) (x2 x)))
	    :in-theory (enable inside-interval-p)
	    ))
   )

 (defthmd cosine-is-1-in-0<2pi=>x=0-5
   (implies (and (realp x)
		 (>= (acl2-pi) x)
		 (>= x 0)
		 (equal (acl2-cosine x) -1))
	    (equal (* x x) (* (acl2-pi) (acl2-pi))))
   :hints (("goal"
	    :cases ((equal x (acl2-pi))
		    (not (equal x (acl2-pi))))
	    )
	   ("subgoal 1"
	    :use ((:instance cosine-is-1-1-on-domain (x1 (acl2-pi)) (x2 x))
		  (:instance cosine-pi))
	    :in-theory (e/d (inside-interval-p) (cosine-pi))
	    )

	   ))
 )

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd cosine-is-1-in-0<2pi=>x=0-2
   (implies (and (realp r)
		 (> r x)
		 (realp x)
		 (>= r 0)
		 (< r (* 2 x)))
	    (equal (mod r x) (- r x))))

 (defthmd cosine-is-1-in-0<2pi=>x=0-3
   (implies (and (realp r)
		 (> r x)
		 (realp x)
		 (>= r 0)
		 (< r (* 2 x)))
	    (and (equal (+ x (mod r x)) r)
		 (> (mod r x) 0)
		 (< (mod r x) x))))

 (defthmd cosine-is-1-in-0<2pi=>x=0-4
   (implies (and (realp x)
		 (< (acl2-pi) x)
		 (< x (* 2 (acl2-pi))))
	    (equal (acl2-cosine x)
		   (- (acl2-cosine (mod x (acl2-pi))))))
   :hints (("goal"
	    :use ((:instance cosine-is-1-in-0<2pi=>x=0-3
			     (r x) (x (acl2-pi)))
		  (:instance cos-pi+x (x (mod x (acl2-pi)))))
	    ))
   )

 (defthmd cosine-is-1-in-0<2pi=>x=0-6
   (implies (and (realp x)
		 (>= x 0)
		 (< x (* 2 (acl2-pi)))
		 (equal (acl2-cosine x) 1))
	    (equal (* x x) 0))
   :hints (("goal"
	    :use ((:instance cosine-is-1-in-0<2pi=>x=0-1 (x x))
		  (:instance cosine-is-1-in-0<2pi=>x=0-4 (x x))
		  (:instance cosine-is-1-in-0<2pi=>x=0-3 (r x) (x (acl2-pi)))
		  (:instance cosine-is-1-in-0<2pi=>x=0-5 (x (mod x (acl2-pi))))
		  )
	    )))
 )

(defthmd sin=0-cos=1
  (implies (and (realp x)
                (>= x 0)
                (< x (* 2 (acl2-pi)))
                (equal (acl2-sine x) 0)
                (equal (acl2-cosine x) 1))
           (equal (* x x) 0))
  :hints (("goal"
           :use ((:instance sine-is-0-in-0<2pi=>x=0orpi-5 (x x))
                 (:instance cosine-is-1-in-0<2pi=>x=0-6 (x x)))
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd cos-2npi-n>=0-1
   (implies (and (integerp n)
		 (equal (acl2-cosine (+ (* 2 (acl2-pi))
					(* 2 (acl2-pi) (+ n -1))))
			1))
	    (equal (acl2-cosine (* 2 (acl2-pi) n)) 1))
   :hints (("goal"
	    :in-theory (disable cosine-of-sums cos-2pi+x cosine-2x)
	    ))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (local
  (defun induction-hint (n)
    (if (and (integerp n)
	     (< 0 n))
	(1+ (induction-hint (+ n -1)))
      1)))

 (local
  (defthm *-x-0
    (equal (* x 0) 0)))

 (local
  (defthm cos-2npi-n>=0
    (implies (and (integerp n)
		  (<= 0 n))
	     (equal (acl2-cosine (* 2 (acl2-pi) n))
		    1))
    :hints (("goal"
	     :induct (induction-hint n))
	    ("subgoal *1/1"
	     :use ((:instance cos-2pi+x (x (* 2 (acl2-pi) (+ n -1))))
		   (:instance cos-2npi-n>=0-1 (n n)))
	     :in-theory nil
	     ))))

 (defthmd cos-2npi
   (implies (integerp n)
	    (equal (acl2-cosine (* 2 (acl2-pi) n))
		   1))
   :hints (("goal"
	    :cases ((< n 0)
		    (= n 0)
		    (> n 0)))
	   ("subgoal 3"
	    :use ((:instance cos-uminus
			     (x (* 2 (acl2-pi) n)))
		  (:instance cos-2npi-n>=0 (n (- n))))
	    :in-theory (disable cos-uminus cos-2npi-n>=0 cosine-2x))))
 )

(defthmd cos2pik+x
  (implies (integerp k)
           (equal (acl2-cosine (+ (* 2 (acl2-pi) k) x))
                  (acl2-cosine x)))
  :hints (("goal"
           :use ((:instance cos-2npi (n k)))
           :in-theory (disable sine-2x)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd sin2pik+x
   (implies (integerp k)
	    (equal (acl2-sine (+ (* 2 (acl2-pi) k) x))
		   (acl2-sine x)))
   :hints (("goal"
	    :use ((:instance sin-2npi (n k))
		  (:instance cos-2npi (n k)))
	    :in-theory (disable sin-2npi cosine-2x sine-2x)
	    )))
 )


(defthmd rotation-a-witn-of0
  (implies (and (point-in-r3 p)
                (point-in-r3 u))
           (m-= (m-* (rotation-3d 0 u) p)
                p))
  :hints (("goal"
           :use ((:instance m-*point-id=point (p1 p))
                 (:instance r-theta-0=id (u u)))
           :in-theory (e/d () (associativity-of-m-* m-* aref2 rotation-3d point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 id-rotation point-in-r3 (:executable-counterpart id-rotation)))
           )))

(defthmd rotation-angle=2pik
  (implies (and (integerp k)
                (point-in-r3 u))
           (equal (rotation-3d (+ (* 2 (acl2-pi) k) x) u)
                  (rotation-3d x u)))
  :hints (("goal"
           :use ((:instance cos2pik+x (k k) (x x))
                 (:instance sin2pik+x (k k) (x x))
                 )
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd integerp-r-mod-r-x/x
   (implies (and (realp r)
		 (not (equal x 0))
		 (realp x))
	    (integerp (/ (- r (mod r x)) x))))
 )

(encapsulate
 ()
 (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd range-mod-r-x
   (implies (and (realp r)
		 (realp x)
		 (> x 0))
	    (and (>= (mod r x) 0)
		 (realp (mod r x))
		 (< (mod r x) x)))
   :hints (("goal"
	    :in-theory (enable mod floor1)
	    )))
 )


(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd realnum-equiv
   (implies (and (realp r)
		 (realp x)
		 (> x 0))
	    (equal (+ (* x (/ (- r (mod r x)) x)) (mod r x))
		   r))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r-theta*p=p=>theta=2kpi
   (implies (and (point-in-r3 p)
		 (point-in-r3 u)
		 (realp angle)
		 (or (not (equal (point-in-r3-x1 p)
				 (point-in-r3-x1 u)))
		     (not (equal (point-in-r3-y1 p)
				 (point-in-r3-y1 u)))
		     (not (equal (point-in-r3-z1 p)
				 (point-in-r3-z1 u))))
		 (or (not (equal (point-in-r3-x1 p)
				 (- (point-in-r3-x1 u))))
		     (not (equal (point-in-r3-y1 p)
				 (- (point-in-r3-y1 u))))
		     (not (equal (point-in-r3-z1 p)
				 (- (point-in-r3-z1 u)))))
		 (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
			   (* (point-in-r3-y1 p) (point-in-r3-y1 p))
			   (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
			1)
		 (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
			   (* (point-in-r3-y1 u) (point-in-r3-y1 u))
			   (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
			1)
		 (equal (point-in-r3-y1 u) 0)
		 (m-= (m-* (rotation-3d angle u) p) p))
	    (equal (* 2 (acl2-pi) (/ (- angle (mod angle (* 2 (acl2-pi)))) (* 2 (acl2-pi))))
		   angle))
   :hints (("goal"
	    :use ((:instance realnum-equiv (r angle) (x (* 2 (acl2-pi))))
		  (:instance integerp-r-mod-r-x/x (r angle) (x (* 2 (acl2-pi))))
		  (:instance range-mod-r-x (r angle) (x (* 2 (acl2-pi))))
		  (:instance rotation-angle=2pik
			     (k (/ (- angle (mod angle (* 2 (acl2-pi)))) (* 2 (acl2-pi))))
			     (u u)
			     (x (mod angle (* 2 (acl2-pi)))))
		  (:instance r-theta*p=p=>sine=0 (p p) (u u) (angle (mod angle (* 2 (acl2-pi)))))
		  (:instance r-theta*p=p=>cosine=1 (p p) (u u) (angle (mod angle (* 2 (acl2-pi)))))
		  (:instance sin=0-cos=1 (x (mod angle (* 2 (acl2-pi))))))
	    :in-theory (e/d () (rotation-3d point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 aref2 m-= mod))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r-theta1*p=r-theta2*p=>r-theta1-theta2*p=p
   (implies (and (realp angle1)
		 (realp angle2)
		 (point-in-r3 u)
		 (point-in-r3 p)
		 (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
			   (* (point-in-r3-y1 u) (point-in-r3-y1 u))
			   (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
			1)
		 (m-= (m-* (rotation-3d angle1 u) p)
		      (m-* (rotation-3d angle2 u) p)))
	    (m-= (m-* (rotation-3d (- angle1 angle2) u) p)
		 p))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2 (angle1 (- angle2)) (angle2 angle1) (u u))
		  (:instance r-t1*r-t2=r-t1+t2 (angle1 (- angle2)) (angle2 angle2) (u u))
		  (:instance r-theta*p=p=>r--theta*p=p-1
			     (m1 (m-* (rotation-3d angle1 u) p))
			     (m2 (m-* (rotation-3d angle2 u) p))
			     (m3 (m-* (rotation-3d (- angle2) u) p)))
		  (:instance r-theta*p=p=>r--theta*p=p-2
			     (m1 (rotation-3d (- angle2) u))
			     (m2 (rotation-3d angle1 u))
			     (m3 p)
			     (m4 (rotation-3d (- angle2) u))
			     (m5 (m-* (rotation-3d angle2 u) p)))
		  (:instance rotation-a-witn-of0 (p p) (u u)))
	    :in-theory (e/d () (aref2 m-= m-* rotation-3d point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1))
	    ))
   )
 )

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd d-p=>d-p-p-1
   (implies (and (s2-def-p p1)
		 (point-in-r3 p2)
		 (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
		 (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
		 (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0))))
	    (s2-def-p p2))
   :hints (("goal"
	    :in-theory (disable aref2)
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd d-p=>d-p-p-2-1
   (implies (r3-matrixp m)
	    (and (equal (aref2 :fake-name (second (f-poles m)) 0 0)
			(- (aref2 :fake-name (first (f-poles m)) 0 0)))
		 (equal (aref2 :fake-name (second (f-poles m)) 1 0)
			(- (aref2 :fake-name (first (f-poles m)) 1 0)))
		 (equal (aref2 :fake-name (second (f-poles m)) 2 0)
			(- (aref2 :fake-name (first (f-poles m)) 2 0)))))
   :hints (("goal"
	    :use ((:instance f-poles-prop-2 (m m)))
	    :in-theory (disable aref2 f-poles acl2-sqrt square)
	    )))

 (defthmd d-p=>d-p-p-2-2
   (implies (and (point-in-r3 p1)
		 (point-in-r3 p2)
		 (equal (aref2 :fake-name p2 0 0) (aref2 :fake-name p1 0 0))
		 (equal (aref2 :fake-name p2 1 0) (aref2 :fake-name p1 1 0))
		 (equal (aref2 :fake-name p2 2 0) (aref2 :fake-name p1 2 0)))
	    (m-= p1 p2))
   :hints (("goal"
	    :in-theory (enable m-=)
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd d-p=>d-p-p-2
   (implies (and (d-p p1)
		 (point-in-r3 p2)
		 (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
		 (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
		 (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0)))
		 (m-= (first (poles (word-exists-witness p1))) p1))
	    (m-= p2 (second (poles (word-exists-witness p1)))))
   :hints (("goal"
	    :use ((:instance s2-def-p (point p1))
		  (:instance point-in-r3 (x p1))
		  (:instance d-p=>d-p-p-2-2 (p1 p2) (p2 (second (poles (word-exists-witness p1)))))
		  (:instance d-p (point p1))
		  (:instance poles (w (word-exists-witness p1)))
		  (:instance word-exists (point p1))
		  (:instance d-p=>d-p-p-2-1 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
		  (:instance r3-rotationp (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
		  (:instance f-poles-prop-3 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
		  (:instance rotation-is-r3-rotationp (w (word-exists-witness p1)) (x (acl2-sqrt 2))))
	    :in-theory (e/d (m-=) (aref2 reducedwordp rotation acl2-sqrt square aref2 m-trans r3-m-inverse r3-m-determinant r3-matrixp f-poles word-exists d-p d-p-implies))
	    ))
   )

 (defthmd d-p=>d-p-p-3
   (implies (and (d-p p1)
		 (point-in-r3 p2)
		 (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
		 (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
		 (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0)))
		 (m-= (second (poles (word-exists-witness p1))) p1))
	    (m-= p2 (first (poles (word-exists-witness p1)))))
   :hints (("goal"
	    :use ((:instance s2-def-p (point p1))
		  (:instance point-in-r3 (x p1))
		  (:instance d-p=>d-p-p-2-2 (p1 p2) (p2 (first (poles (word-exists-witness p1)))))
		  (:instance d-p (point p1))
		  (:instance poles (w (word-exists-witness p1)))
		  (:instance word-exists (point p1))
		  (:instance d-p=>d-p-p-2-1 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
		  (:instance r3-rotationp (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
		  (:instance f-poles-prop-3 (m (rotation (word-exists-witness p1) (acl2-sqrt 2))))
		  (:instance rotation-is-r3-rotationp (w (word-exists-witness p1)) (x (acl2-sqrt 2))))
	    :in-theory (e/d (m-=) (aref2 reducedwordp rotation acl2-sqrt square aref2 m-trans r3-m-inverse r3-m-determinant r3-matrixp f-poles word-exists d-p d-p-implies))
	    ))
   )
 )

(defthmd d-p=>d-p-p-4
  (implies (and (m-= p2 pole)
                (m-= (m-* rot pole) pole))
           (m-= (m-* rot p2) p2)))

(defthmd d-p=>d-p-p
  (implies (and (d-p p1)
                (point-in-r3 p2)
                (equal (aref2 :fake-name p2 0 0) (- (aref2 :fake-name p1 0 0)))
                (equal (aref2 :fake-name p2 1 0) (- (aref2 :fake-name p1 1 0)))
                (equal (aref2 :fake-name p2 2 0) (- (aref2 :fake-name p1 2 0))))
           (d-p p2))
  :hints (("goal"
           :use ((:instance two-poles-for-all-rotations (p p1)))
           :cases ((m-= (first (poles (word-exists-witness p1))) p1)
                   (m-= (second (poles (word-exists-witness p1))) p1))
           :in-theory (disable reducedwordp d-p word-exists square s2-def-p wordp array2p word-exists-suff)
           )
          ("subgoal 2"
           :use ((:instance d-p=>d-p-p-2 (p1 p1) (p2 p2))
                 (:instance d-p (point p1))
                 (:instance d-p (point p2))
                 (:instance word-exists-suff (point p2) (w (word-exists-witness p1)))
                 (:instance word-exists (point p1))
                 (:instance d-p=>d-p-p-1 (p1 p1) (p2 p2))
                 (:instance f-returns-poles-1-second (w  (word-exists-witness p1)))
                 (:instance d-p=>d-p-p-4 (p2 p2) (pole (second (poles (word-exists-witness p1))))
                            (rot (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                 )
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance d-p=>d-p-p-3 (p1 p1) (p2 p2))
                 (:instance d-p (point p1))
                 (:instance d-p (point p2))
                 (:instance word-exists-suff (point p2) (w (word-exists-witness p1)))
                 (:instance word-exists (point p1))
                 (:instance d-p=>d-p-p-1 (p1 p1) (p2 p2))
                 (:instance f-returns-poles-1-first (w  (word-exists-witness p1)))
                 (:instance d-p=>d-p-p-4 (p2 p2) (pole (first (poles (word-exists-witness p1))))
                            (rot (rotation (word-exists-witness p1) (acl2-sqrt 2))))
                 )
           :in-theory nil
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd diff-d-p-p=>d-p-p1
   (implies (and (d-p p)
		 (point-in-r3 p1)
		 (m-= p p1))
	    (d-p p1))
   :hints (("goal"
	    :use ((:instance d-p (point p1))
		  (:instance word-exists-suff (w (word-exists-witness p)) (point p1))
		  (:instance d-p-p=>d-p-p1-lemma (m1 (rotation (word-exists-witness p) (acl2-sqrt 2)))
			     (m2 p) (m3 p1))
		  (:instance s2-def-p-p=>p1 (p p) (p1 p1)))

	    :in-theory (e/d () (m-* acl2-sqrt reducedwordp rotation r3-rotationp acl2-sqrt word-exists-suff d-p))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd d-p-not-equal-to-u-n-u
   (implies (and (d-p p)
		 (point-in-r3 u)
		 (not (d-p u))
		 (point-in-r3 m-u)
		 (equal (aref2 :fake-name m-u 0 0)
			(- (aref2 :fake-name u 0 0)))
		 (equal (aref2 :fake-name m-u 1 0)
			(- (aref2 :fake-name u 1 0)))
		 (equal (aref2 :fake-name m-u 2 0)
			(- (aref2 :fake-name u 2 0)))
		 )
	    (and (not (m-= p u))
		 (not (m-= p m-u))))
   :hints (("goal"
	    :use ((:instance diff-d-p-p=>d-p-p1 (p p) (p1 u))
		  (:instance diff-d-p-p=>d-p-p1 (p p) (p1 m-u))
		  (:instance d-p=>d-p-p (p1 m-u) (p2 u)))
	    :in-theory (e/d () (m-* acl2-sqrt reducedwordp rotation r3-rotationp acl2-sqrt word-exists-suff d-p))
	    )))
 )

(defthmd d-p=>notm-=u--u
  (implies (and (d-p p)
                (point-in-r3 u)
                (not (d-p u)))
           (and (not (m-= p u))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-y1 p)
                                (- (point-in-r3-y1 u))))
                    (not (equal (point-in-r3-z1 p)
                                (- (point-in-r3-z1 u)))))))
  :hints (("goal"
           :use ((:instance diff-d-p-p=>d-p-p1 (p p) (p1 u))
                 (:instance d-p=>d-p-p (p1 p) (p2 u)))
           :in-theory (e/d (m-=) (d-p))
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/inequalities" :dir :system))
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-1
   (implies (and (realp angle)
		 (integerp k)
		 (< angle (* 2 (acl2-pi))))
	    (< (+ (* 2 (acl2-pi) k) angle) (+ (* 2 (acl2-pi) k) (* 2 (acl2-pi))))))

 (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-2
   (implies (and (realp angle)
		 (integerp k)
		 (< angle (* 2 (acl2-pi)))
		 (>= (+ (* 2 (acl2-pi) k) angle) 0))
	    (> (+ (* 2 (acl2-pi) k) (* 2 (acl2-pi))) 0))
   :hints (("goal"
	    :use ((:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-1))
	    )))

 (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-3
   (implies (and (integerp k)
		 (> (+ (* 2 (acl2-pi) k) (* 2 (acl2-pi))) 0))
	    (> k -1)))

 (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-4
   (implies (and (realp angle)
		 (integerp k)
		 (>= angle 0))
	    (>= (+ (* 2 (acl2-pi) k) angle) (* 2 (acl2-pi) k))))

 (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-5
   (implies (and (realp angle)
		 (integerp k)
		 (>= angle 0)
		 (< (+ (* 2 (acl2-pi) k) angle) (* 2 (acl2-pi))))
	    (< (* 2 (acl2-pi) k) (* 2 (acl2-pi))))
   :hints (("goal"
	    :use ((:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-4))
	    )))

 (defthmd r-theta1*p1=r-theta2*p1=>theta1=theta2-6
   (implies (and (integerp k)
		 (< (* 2 (acl2-pi) k) (* 2 (acl2-pi))))
	    (< k 1)))

 (defthm r-theta1*p1=r-theta2*p1=>theta1=theta2-7
   (implies (and (realp angle)
		 (integerp k)
		 (< angle (* 2 (acl2-pi)))
		 (>= angle 0)
		 (>= (+ (* 2 (acl2-pi) k) angle) 0)
		 (< (+ (* 2 (acl2-pi) k) angle) (* 2 (acl2-pi))))
	    (equal k 0))
   :hints (("goal"
	    :use ((:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-2)
		  (:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-3)
		  (:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-5)
		  (:instance r-theta1*p1=r-theta2*p1=>theta1=theta2-6))
	    ))
   :rule-classes nil)
 )

(defun pole-seq (n)
  (if (posp n)
      (nth (- n 1) (poles-list (generate-words-main n)))
    0))

(defun-sk nth-pole-exists (p)
  (exists n
          (and (posp n)
               (m-= (pole-seq n) p))))


(defthmd poles-countable-thm
  (implies (d-p p)
           (nth-pole-exists p))
  :hints (("goal"
           :use ((:instance exists-pole-n-thm (p p))
                 (:instance exists-pole-n (pole p))
                 (:instance nth-pole-exists-suff (p p) (n (+ (exists-pole-n-witness p) 1))))
           :in-theory (e/d () (poles-list generate-words-main))
           )))

(defun p1-*-p2-seq-i (i)
  (let ((rm-2 (mod-remainder-2 0 i)))
    (let ((rm-3 (mod-remainder-3 0 (nth 1 rm-2))))
      (if (equal (nth 1 rm-3) 1)
          (list (list (pole-seq (nth 0 rm-2)) (pole-seq (nth 0 rm-3))))
        (list (list (pole-seq (nth 0 rm-2)) (pole-seq (nth 0 rm-3))))))))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defun p1*p2-seq-2 (i)
   (if (zp i)
       nil
     (append (p1*p2-seq-2 (- i 1)) (p1-*-p2-seq-i i))))
 )

(defun p1-*-p2-seq (i)
  (if (posp i)
      (p1*p2-seq-2 i)
    nil))

(defun p1-*-p2-sequence (n)
  (if (posp n)
      (nth (- n 1) (p1-*-p2-seq n))
    (list (pole-seq 0) (pole-seq 0))))

(defun-sk p1-*-p2-countable (x)
  (exists n
          (and (posp n)
               (equal (p1-*-p2-sequence n) x))))

(defthmd p1-*-p2-seq-exists
  (implies (and (posp n1)
                (posp n2)
                (equal (pole-seq n1) p)
                (equal (pole-seq n2) q))
           (p1-*-p2-countable (list p q)))
  :hints (("goal"
           :use (:functional-instance f-*-g-seq-exists
                                      (f pole-seq)
                                      (g pole-seq)
                                      (f-*-g-countable p1-*-p2-countable)
                                      (f-*-g-sequence p1-*-p2-sequence)
                                      (f-*-g-seq p1-*-p2-seq)
                                      (f-*-g-seq-2 p1*p2-seq-2)
                                      (f-*-g-seq-i p1-*-p2-seq-i)
                                      (f-*-g-countable-witness p1-*-p2-countable-witness))
           )))

(defun natp-seq (n)
  (if (posp n)
      (- n 1)
    0))

(defun-sk num>=0-exists (num)
  (exists n
          (and (posp n)
               (equal (natp-seq n) num))))


(defthmd natnum-countable-thm
  (implies (natp num)
           (num>=0-exists num))
  :hints (("goal"
           :use (:instance num>=0-exists-suff (n (+ num 1)) (num num))
           )))

(defun p1p2-n-seq-i (i)
  (let ((rm-2 (mod-remainder-2 0 i)))
    (let ((rm-3 (mod-remainder-3 0 (nth 1 rm-2))))
      (if (equal (nth 1 rm-3) 1)
          (list (list (p1-*-p2-sequence (nth 0 rm-2)) (natp-seq (nth 0 rm-3))))
        (list (list (p1-*-p2-sequence (nth 0 rm-2)) (natp-seq (nth 0 rm-3))))))))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defun p1p2-n-seq-2 (i)
   (if (zp i)
       nil
     (append (p1p2-n-seq-2 (- i 1)) (p1p2-n-seq-i i))))
 )

(defun p1p2-n-seq (i)
  (if (posp i)
      (p1p2-n-seq-2 i)
    nil))

(defun p1p2-n-sequence (n)
  (if (posp n)
      (nth (- n 1) (p1p2-n-seq n))
    (list (p1-*-p2-sequence 0) (natp-seq 0))))

(defun-sk p1p2-n-countable (x)
  (exists n
          (and (posp n)
               (equal (p1p2-n-sequence n) x))))

(defthmd p1p2-n-seq-exists
  (implies (and (posp n1)
                (posp n2)
                (equal (p1-*-p2-sequence n1) p)
                (equal (natp-seq n2) q))
           (p1p2-n-countable (list p q)))
  :hints (("goal"
           :use (:functional-instance f-*-g-seq-exists
                                      (f p1-*-p2-sequence)
                                      (g natp-seq)
                                      (f-*-g-countable p1p2-n-countable)
                                      (f-*-g-sequence p1p2-n-sequence)
                                      (f-*-g-seq p1p2-n-seq)
                                      (f-*-g-seq-2 p1p2-n-seq-2)
                                      (f-*-g-seq-i p1p2-n-seq-i)
                                      (f-*-g-countable-witness p1p2-n-countable-witness))
           )))

(defun posp-seq (n)
  (if (posp n)
      n
    0))

(defun-sk num>=1-exists (num)
  (exists n
          (and (posp n)
               (equal (posp-seq n) num))))


(defthmd posp-countable-thm
  (implies (posp num)
           (num>=1-exists num))
  :hints (("goal"
           :use (:instance num>=1-exists-suff (n num) (num num))
           )))

(defun p1p2-n-p-seq-i (i)
  (let ((rm-2 (mod-remainder-2 0 i)))
    (let ((rm-3 (mod-remainder-3 0 (nth 1 rm-2))))
      (if (equal (nth 1 rm-3) 1)
          (list (list (p1p2-n-sequence (nth 0 rm-2)) (posp-seq (nth 0 rm-3))))
        (list (list (p1p2-n-sequence (nth 0 rm-2)) (posp-seq (nth 0 rm-3))))))))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defun p1p2-n-p-seq-2 (i)
   (if (zp i)
       nil
     (append (p1p2-n-p-seq-2 (- i 1)) (p1p2-n-p-seq-i i))))
 )

(defun p1p2-n-p-seq (i)
  (if (posp i)
      (p1p2-n-p-seq-2 i)
    nil))

(defun p1p2-n-p-sequence (n)
  (if (posp n)
      (nth (- n 1) (p1p2-n-p-seq n))
    (list (p1p2-n-sequence 0) (posp-seq 0))))

(defun-sk p1p2-n-p-countable (x)
  (exists n
          (and (posp n)
               (equal (p1p2-n-p-sequence n) x))))

(defthmd p1p2-n-p-seq-exists
  (implies (and (posp n1)
                (posp n2)
                (equal (p1p2-n-sequence n1) p)
                (equal (posp-seq n2) q))
           (p1p2-n-p-countable (list p q)))
  :hints (("goal"
           :use (:functional-instance f-*-g-seq-exists
                                      (f p1p2-n-sequence)
                                      (g posp-seq)
                                      (f-*-g-countable p1p2-n-p-countable)
                                      (f-*-g-sequence p1p2-n-p-sequence)
                                      (f-*-g-seq p1p2-n-p-seq)
                                      (f-*-g-seq-2 p1p2-n-p-seq-2)
                                      (f-*-g-seq-i p1p2-n-p-seq-i)
                                      (f-*-g-countable-witness p1p2-n-p-countable-witness))
           )))

(defthmd p1p2-n-p-in-the-list
  (implies (and (posp n1)
                (posp n2)
                (posp n3)
                (posp n4)
                (equal (pole-seq n1) p1)
                (equal (pole-seq n2) p2)
                (equal (natp-seq n3) nat)
                (equal (posp-seq n4) pos))
           (p1p2-n-p-countable (list (list (list p1 p2) nat) pos)))
  :hints (("goal"
           :use ((:instance p1-*-p2-seq-exists (n1 n1) (n2 n2) (p (pole-seq n1)) (q (pole-seq n2)))
                 (:instance p1p2-n-seq-exists (n1 (p1-*-p2-countable-witness (list p1 p2)))
                            (p (list (pole-seq n1) (pole-seq n2)))
                            (q (natp-seq n3))
                            (n2 n3))
                 (:instance p1p2-n-p-seq-exists
                            (n1 (p1p2-n-countable-witness (list (list (pole-seq n1) (pole-seq n2)) nat)))
                            (p (list (list (pole-seq n1) (pole-seq n2)) nat))
                            (q (posp-seq n4))
                            (n2 n4))
                 (:instance p1-*-p2-countable (x (list (pole-seq n1) (pole-seq n2))))
                 (:instance p1p2-n-countable (x (list (list (pole-seq n1) (pole-seq n2))
                                                      (natp-seq n3))))
                 )
           :in-theory nil
           )))

(defun-sk exists-angle>=0<2pi (p1 p2)
  (exists angle
          (and (realp angle)
               (>= angle 0)
               (< angle (* 2 (acl2-pi)))
               (m-= (m-* (rotation-3d angle (point-on-s2-not-d)) p1) p2))))

(defun angle-p1p2 (angle nat pos)
  (/ (+ (* 2 (acl2-pi) nat) angle) pos))

(defun generate-angles (n)
  (if (zp n)
      nil
    (let ((p1 (caaar (p1p2-n-p-sequence n)))
          (p2 (cadaar (p1p2-n-p-sequence n)))
          (nat (cadar (p1p2-n-p-sequence n)))
          (pos (cadr (p1p2-n-p-sequence n))))
      (if (exists-angle>=0<2pi p1 p2)
          (append (generate-angles (- n 1)) (list (angle-p1p2 (exists-angle>=0<2pi-witness p1 p2) nat pos)))
        (append (generate-angles (- n 1)) (list 0))))))

(defthmd realp-angle-p1p2
  (implies (and (realp angle)
                (realp nat)
                (realp pos))
           (realp (angle-p1p2 angle nat pos))))

(defun angles-seq (n)
  (if (posp n)
      (nth (- n 1) (generate-angles n))
    0))

(defun-sk nth-angle-exists (angle)
  (exists n
          (and (posp n)
               (equal (angles-seq n) angle))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd generate-angles-lemma1
   (implies (natp n)
	    (equal (len (generate-angles n)) n))
   :hints (("goal"
	    :in-theory (disable p1p2-n-p-sequence rotation-3d point-on-s2-not-d)
	    :induct (generate-angles n)
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd angles-countable-thm-1
   (implies (and (posp (- n 1))
		 (natp q)
		 (< q (len (generate-angles (- n 1)))))
	    (equal (nth q (generate-angles n))
		   (nth q (generate-angles (- n 1)))))
   :hints (("goal"
	    :in-theory (disable p1p2-n-p-sequence rotation-3d point-on-s2-not-d angle-p1p2)
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthm angles-countable-thm-2-sub*1/3-sub1-1
   (implies (and (natp q)
		 (posp n)
		 (not (posp (- n 1)))
		 (< q (len (generate-angles n))))
	    (and (equal q 0)
		 (equal n 1)))
   :hints (("goal"
	    :use ((:instance generate-angles-lemma1 (n n)))
	    :in-theory (disable angle-p1p2 exists-angle>=0<2pi p1p2-n-p-sequence generate-angles)
	    ))
   :rule-classes nil)

 (defthmd angles-countable-thm-2-sub*1/3-sub1-2
   (equal (nth 0 (generate-angles 1))
	  (let ((p1 (car (car (car (p1p2-n-p-sequence (+ 0 1))))))
		(p2 (cadr (car (car (p1p2-n-p-sequence (+ 0 1))))))
		(nat (cadr (car (p1p2-n-p-sequence (+ 0 1)))))
		(pos (cadr (p1p2-n-p-sequence (+ 0 1)))))
	    (if (exists-angle>=0<2pi p1 p2)
		(angle-p1p2 (exists-angle>=0<2pi-witness p1 p2)
			    nat pos)
	      0)))
   :hints (("goal"
	    :use ((:instance generate-angles (n 1)))
	    :cases ((exists-angle>=0<2pi (car (car (car (p1p2-n-p-sequence (+ 0 1)))))
					 (cadr (car (car (p1p2-n-p-sequence (+ 0 1)))))))
	    :in-theory (disable angle-p1p2 exists-angle>=0<2pi p1p2-n-p-sequence generate-angles)
	    )))

 (defthmd angles-countable-thm-2-sub*1/3
   (implies
    (and
     (not (zp n))
     (not (exists-angle>=0<2pi (car (car (car (p1p2-n-p-sequence n))))
			       (cadr (car (car (p1p2-n-p-sequence n))))))
     (implies (and (posp (+ -1 n))
		   (natp q)
		   (< q (len (generate-angles (+ -1 n)))))
	      (equal (nth q (generate-angles (+ -1 n)))
		     (let ((p1 (car (car (car (p1p2-n-p-sequence (+ q 1))))))
			   (p2 (cadr (car (car (p1p2-n-p-sequence (+ q 1))))))
			   (nat (cadr (car (p1p2-n-p-sequence (+ q 1)))))
			   (pos (cadr (p1p2-n-p-sequence (+ q 1)))))
		       (if (exists-angle>=0<2pi p1 p2)
			   (angle-p1p2 (exists-angle>=0<2pi-witness p1 p2)
				       nat pos)
			 0)))))
    (implies (and (posp n)
		  (natp q)
		  (< q (len (generate-angles n))))
	     (equal (nth q (generate-angles n))
		    (let ((p1 (car (car (car (p1p2-n-p-sequence (+ q 1))))))
			  (p2 (cadr (car (car (p1p2-n-p-sequence (+ q 1))))))
			  (nat (cadr (car (p1p2-n-p-sequence (+ q 1)))))
			  (pos (cadr (p1p2-n-p-sequence (+ q 1)))))
		      (if (exists-angle>=0<2pi p1 p2)
			  (angle-p1p2 (exists-angle>=0<2pi-witness p1 p2)
				      nat pos)
			0)))))
   :hints (("goal"
	    :cases ((not (posp (- n 1))))
	    :in-theory (disable angle-p1p2 exists-angle>=0<2pi p1p2-n-p-sequence generate-angles)
	    :do-not-induct t
	    )
	   ("subgoal 2"
	    :use ((:instance angles-countable-thm-1 (n n) (q q))
		  (:instance generate-angles-lemma1 (n n))
		  (:instance generate-angles (n n))
		  (:instance generate-angles-lemma1 (n (- n 1))))
	    )
	   ("subgoal 1"
	    :use ((:instance angles-countable-thm-2-sub*1/3-sub1-1)
		  (:instance angles-countable-thm-2-sub*1/3-sub1-2))
	    )
	   ))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd angles-countable-thm-2
   (implies (and (posp n)
		 (natp q)
		 (< q (len (generate-angles n))))
	    (equal (nth q (generate-angles n))
		   (let ((p1 (caaar (p1p2-n-p-sequence (+ q 1))))
			 (p2 (cadaar (p1p2-n-p-sequence (+ q 1))))
			 (nat (cadar (p1p2-n-p-sequence (+ q 1))))
			 (pos (cadr (p1p2-n-p-sequence (+ q 1)))))
		     (if (exists-angle>=0<2pi p1 p2)
			 (angle-p1p2 (exists-angle>=0<2pi-witness p1 p2) nat pos)
		       0))))
   :hints (("goal"
	    :in-theory (disable p1p2-n-p-sequence rotation-3d point-on-s2-not-d angle-p1p2)
	    )
	   ("subgoal *1/3"
	    :use ((:instance angles-countable-thm-2-sub*1/3))
	    )
	   ("subgoal *1/2"
	    :use ((:instance angles-countable-thm-1 (n n) (q q))
		  (:instance generate-angles-lemma1 (n n))
		  (:instance generate-angles-lemma1 (n (- n 1))))
	    )
	   ))
 )

(defthmd angles-countable-thm
  (implies (and (posp n1)
                (posp n2)
                (posp n3)
                (posp n4)
                (equal (pole-seq n1) p1)
                (equal (pole-seq n2) p2)
                (equal (natp-seq n3) nat)
                (equal (posp-seq n4) pos)
                (realp angle)
                (>= angle 0)
                (< angle (* 2 (acl2-pi)))
                (m-= (m-* (rotation-3d angle (point-on-s2-not-d)) p1) p2))
           (nth-angle-exists (/ (+ (* 2 (acl2-pi) nat) (exists-angle>=0<2pi-witness p1 p2)) pos)))
  :hints (("goal"
           :use ((:instance p1p2-n-p-in-the-list (n1 n1) (n2 n2) (n3 n3) (n4 n4)
                            (p1 (pole-seq n1))
                            (p2 (pole-seq n2))
                            (nat (natp-seq n3))
                            (pos (posp-seq n4)))
                 (:instance angles-countable-thm-2
                            (q (- (p1p2-n-p-countable-witness (list (list (list p1 p2) nat) pos)) 1))
                            (n (p1p2-n-p-countable-witness (list (list (list p1 p2) nat) pos))))
                 (:instance generate-angles-lemma1
                            (n (p1p2-n-p-countable-witness (list (list (list p1 p2) nat) pos))))
                 (:instance nth-angle-exists-suff
                            (n (p1p2-n-p-countable-witness (list (list (list p1 p2) nat) pos)))
                            (angle angle))
                 (:instance exists-angle>=0<2pi-suff (p1 p1) (p2 p2)
                            (angle angle)))
           :in-theory (e/d () (p1p2-n-p-sequence pole-seq point-on-s2-not-d rotation-3d natp-seq posp-seq m-* m-= acl2-sqrt))
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/inequalities" :dir :system))

 (defthmd k-range-1
   (implies (and (integerp y)
		 (>= y (- x))
		 (< x 1))
	    (>= y 0)))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd k-range-2
   (implies (and (posp n)
		 (realp x)
		 (realp angle)
		 (>= angle 0)
		 (< angle (* 2 (acl2-pi)))
		 (>= x 0)
		 (integerp k)
		 (< x (* 2 (acl2-pi)))
		 (equal (* n angle)
			(+ (* 2 (acl2-pi) k) x)))
	    (equal (/ (- (* n angle) x) (* 2 (acl2-pi))) k)))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/inequalities" :dir :system))

 (defthmd k-range-3
   (implies (and (posp n)
		 (realp x)
		 (realp angle)
		 (>= angle 0)
		 (< angle (* 2 (acl2-pi)))
		 (>= x 0)
		 (integerp k)
		 (< x (* 2 (acl2-pi)))
		 (equal (* n angle)
			(+ (* 2 (acl2-pi) k) x)))
	    (>= k 0))
   :hints (("goal"
	    :use ((:instance k-range-1 (y k) (x (/ x (* 2 (acl2-pi)))))
		  (:instance k-range-2 (n n) (x x) (angle angle) (k k)))
	    )))
 )

(defthm r-theta*p=p=>angle>=0<2pi=>0
  (implies (and (point-in-r3 p)
                (point-in-r3 u)
                (realp angle)
                (or (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-y1 p)
                                (point-in-r3-y1 u)))
                    (not (equal (point-in-r3-z1 p)
                                (point-in-r3-z1 u))))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-y1 p)
                                (- (point-in-r3-y1 u))))
                    (not (equal (point-in-r3-z1 p)
                                (- (point-in-r3-z1 u)))))
                (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (equal (point-in-r3-y1 u) 0)
                (>= angle 0)
                (< angle (* 2 (acl2-pi)))
                (m-= (m-* (rotation-3d angle u) p) p))
           (equal angle 0))
  :hints (("goal"
           :use ((:instance r-theta*p=p=>cosine=1 (p p) (u u))
                 (:instance r-theta*p=p=>sine=0 (p p) (u u))
                 (:instance sin=0-cos=1 (x angle)))
           :in-theory (e/d () (m-= m-* rotation-3d point-in-r3-x1 point-in-r3-y1 point-in-r3-z1))
           ))
  :rule-classes nil)

(defthm r-theta1*p=p-r-theta2*p=p=>1=2
  (implies (and (realp angle1)
                (realp angle2)
                (>= angle1 0)
                (< angle1 (* 2 (acl2-pi)))
                (>= angle2 0)
                (< angle2 (* 2 (acl2-pi)))
                (point-in-r3 p)
                (point-in-r3 u)
                (or (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-y1 p)
                                (point-in-r3-y1 u)))
                    (not (equal (point-in-r3-z1 p)
                                (point-in-r3-z1 u))))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-y1 p)
                                (- (point-in-r3-y1 u))))
                    (not (equal (point-in-r3-z1 p)
                                (- (point-in-r3-z1 u)))))
                (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1)
                (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (equal (point-in-r3-y1 u) 0)
                (m-= (m-* (rotation-3d angle1 u) p)
                     (m-* (rotation-3d angle2 u) p)))
           (equal angle1 angle2))
  :hints (("goal"
           :use ((:instance r-theta1*p=r-theta2*p=>r-theta1-theta2*p=p (angle1 angle1)
                            (angle2 angle2)
                            (u u) (p p))
                 (:instance r-theta1*p=r-theta2*p=>r-theta1-theta2*p=p (angle1 angle2)
                            (angle2 angle1)
                            (u u) (p p))
                 (:instance r-theta*p=p=>angle>=0<2pi=>0 (p p) (u u) (angle (- angle1 angle2)))
                 (:instance r-theta*p=p=>angle>=0<2pi=>0 (p p) (u u) (angle (- angle2 angle1))))
           :in-theory (e/d () (m-= m-* rotation-3d point-in-r3-x1 point-in-r3-y1 point-in-r3-z1))
           ))
  :rule-classes nil)

(defthmd point-on-s2-not-d-on-s2
  (implies (equal (point-on-s2-not-d) u)
           (and (equal (+ (* (point-in-r3-x1 u) (point-in-r3-x1 u))
                          (* (point-in-r3-y1 u) (point-in-r3-y1 u))
                          (* (point-in-r3-z1 u) (point-in-r3-z1 u)))
                       1)
                (not (d-p u))))
  :hints (("goal"
           :use ((:instance r3-rotationp-r-theta-2 (point (point-on-s2-not-d)))
                 (:instance r3-rotationp-r-theta-5 (point (point-on-s2-not-d)))
                 (:instance exists-in-x-coord-sequence-lemma (p u))
                 (:instance exists-point-on-s2-not-d-3)
                 (:instance witness-not-in-x-coord-sequence))
           :in-theory (disable point-on-s2-not-d point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 aref2 d-p)
           )))

(defthmd d-p=>notm-=u--u-1
  (implies (and (d-p p)
                (point-in-r3 u)
                (not (d-p u)))
           (and (or (not (equal (point-in-r3-x1 p)
                                (point-in-r3-x1 u)))
                    (not (equal (point-in-r3-y1 p)
                                (point-in-r3-y1 u)))
                    (not (equal (point-in-r3-z1 p)
                                (point-in-r3-z1 u))))
                (or (not (equal (point-in-r3-x1 p)
                                (- (point-in-r3-x1 u))))
                    (not (equal (point-in-r3-y1 p)
                                (- (point-in-r3-y1 u))))
                    (not (equal (point-in-r3-z1 p)
                                (- (point-in-r3-z1 u)))))))
  :hints (("goal"
           :use ((:instance d-p=>notm-=u--u (p p) (u u)))
           :in-theory (e/d (m-=) (word-exists))
           )))

(defthm r-theta1*p=p-r-theta2*p=p=>1=2-d-p-1
  (implies (d-p p)
           (and (equal (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                       1)
                (point-in-r3 p))))

(defthm r-theta1*p=p-r-theta2*p=p=>1=2-d-p
  (implies (and (realp angle1)
                (realp angle2)
                (>= angle1 0)
                (< angle1 (* 2 (acl2-pi)))
                (>= angle2 0)
                (< angle2 (* 2 (acl2-pi)))
                (d-p p)
                (equal (point-on-s2-not-d) u)
                (m-= (m-* (rotation-3d angle1 u) p)
                     (m-* (rotation-3d angle2 u) p)))
           (equal angle1 angle2))
  :hints (("goal"
           :use ((:instance r-theta1*p=p-r-theta2*p=p=>1=2 (angle1 angle1)
                            (angle2 angle2)
                            (u (point-on-s2-not-d)) (p p))
                 (:instance d-p (point p))
                 (:instance s2-def-p (point p))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point u))
                 (:instance r3-rotationp-r-theta-5 (point (point-on-s2-not-d)))
                 (:instance r-theta1*p=p-r-theta2*p=p=>1=2-d-p-1 (p p))
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance d-p=>notm-=u--u-1 (p p) (u (point-on-s2-not-d))))
           :in-theory nil
           ))
  :rule-classes nil)

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd angles-countable-1
   (implies (and (realp angle)
		 (posp n)
		 (>= angle 0)
		 (< angle (* 2 (acl2-pi))))
	    (and (natp (* (+ (* n angle)
			     (- (mod (* n angle) (* 2 (acl2-pi)))))
			  (/ (* 2 (acl2-pi)))))
		 (realp (mod (* n angle) (* 2 (acl2-pi))))
		 (realp (* n angle))
		 (realp (* 2 (acl2-pi)))))
   :hints (("goal"
	    :use (:instance k-range-3 (n n) (x (mod (* n angle) (* 2 (acl2-pi)))) (angle angle)
			    (k (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
				  (* 2 (acl2-pi)))))
	    )))

 (defthmd angles-countable-2
   (implies (and (d-p p1)
		 (d-p p2)
		 (nth-pole-exists p1)
		 (nth-pole-exists p2)
		 (exists-angle>=0<2pi p1 p2))
	    (and (realp (exists-angle>=0<2pi-witness p1 p2))
		 (m-= (pole-seq (nth-pole-exists-witness p1)) p1)
		 (m-= (pole-seq (nth-pole-exists-witness p2)) p2)
		 (posp (nth-pole-exists-witness p1))
		 (posp (nth-pole-exists-witness p2))))
   :hints (("goal"
	    :in-theory (disable d-p)
	    )))
 )

(defthmd angles-countable-3
  (implies (and (d-p p1)
                (d-p p2)
                (realp angle)
                (posp n)
                (>= angle 0)
                (< angle (* 2 (acl2-pi)))
                (m-= (m-* (rotation-3d (* n angle) (point-on-s2-not-d)) p1) p2))
           (m-= (m-* (rotation-3d (mod (* n angle) (* 2 (acl2-pi)))
                                  (point-on-s2-not-d))
                     p1)
                p2))
  :hints (("goal"
           :use ((:instance realnum-equiv (r (* n angle)) (x (* 2 (acl2-pi))))
                 (:instance k-range-3 (n n) (x (mod (* n angle) (* 2 (acl2-pi)))) (angle angle)
                            (k (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                  (* 2 (acl2-pi)))))
                 (:instance integerp-r-mod-r-x/x (r (* n angle)) (x (* 2 (acl2-pi))))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance rotation-angle=2pik
                            (k (* (+ (* n angle)
                                     (- (mod (* n angle) (* 2 (acl2-pi)))))
                                  (/ (* 2 (acl2-pi)))))
                            (x (mod (* n angle) (* 2 (acl2-pi))))
                            (u (point-on-s2-not-d))))
           :in-theory (disable rotation-3d point-on-s2-not-d acl2-sqrt word-exists d-p)
           )))

(defthmd angles-countable-4
  (implies (num>=0-exists p)
           (posp (num>=0-exists-witness p))))

(defthmd angles-countable-5
  (implies (num>=1-exists n)
           (posp (num>=1-exists-witness n))))

(defthmd angles-countable-6
  (implies (num>=0-exists p)
           (equal (natp-seq (num>=0-exists-witness p)) p)))

(defthmd angles-countable-7
  (implies (num>=1-exists n)
           (equal (posp-seq (num>=1-exists-witness n)) n)))

(defthmd angles-countable-8
  (implies (and (m-= witp1 p1)
                (m-= witp2 p2)
                (m-= (m-* p3 p1) p2))
           (m-= (m-* p3 witp1) witp2)))

(defthmd angles-countable-9
  (implies (exists-angle>=0<2pi p1 p2)
           (and (realp (exists-angle>=0<2pi-witness p1 p2))
                (>= (exists-angle>=0<2pi-witness p1 p2) 0)
                (< (exists-angle>=0<2pi-witness p1 p2) (* 2 (acl2-pi)))
                (m-= (m-* (rotation-3d (exists-angle>=0<2pi-witness p1 p2)
                                       (point-on-s2-not-d)) p1) p2)))
  :hints (("goal"
           :in-theory (disable rotation-3d)
           )))

(defthmd angles-countable-10
  (implies (and (m-= (m-* x p1) p2)
                (m-= (m-* y witp1) witp2)
                (m-= witp1 p1)
                (m-= witp2 p2))
           (m-= (m-* x p1) (m-* y p1))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm angles-countable-11
   (implies (and (posp n)
		 (realp angle)
		 (equal (+ (* (* 2 (acl2-pi))
			      (+ (* n angle)
				 (- (exists-angle>=0<2pi-witness p1 p2)))
			      (/ (* 2 (acl2-pi))))
			   (exists-angle>=0<2pi-witness p1 p2))
			(* n angle)))
	    (equal angle
		   (* (+ (* 2 (acl2-pi)
			    (+ (* n angle)
			       (- (exists-angle>=0<2pi-witness p1 p2)))
			    (/ (* 2 (acl2-pi))))
			 (exists-angle>=0<2pi-witness p1 p2))
		      (/ n))))
   :rule-classes nil)
 )

(defthmd angles-countable-12
  (implies
   (equal (+ (* (* 2 (acl2-pi))
                (+ (* n angle)
                   (- (exists-angle>=0<2pi-witness p1 p2)))
                (/ (* 2 (acl2-pi))))
             (exists-angle>=0<2pi-witness p1 p2))
          (* n angle))
   (equal (* n angle)
          (+ (* 2 (acl2-pi)
                (+ (* n angle)
                   (- (exists-angle>=0<2pi-witness p1 p2)))
                (/ (* 2 (acl2-pi))))
             (exists-angle>=0<2pi-witness p1 p2)))))

(defthmd angles-countable
  (implies (and (d-p p1)
                (d-p p2)
                (realp angle)
                (posp n)
                (>= angle 0)
                (< angle (* 2 (acl2-pi)))
                (m-= (m-* (rotation-3d (* n angle) (point-on-s2-not-d)) p1) p2))
           (nth-angle-exists angle))
  :hints (("goal"
           :use ((:instance poles-countable-thm (p p1))
                 (:instance poles-countable-thm (p p2))
                 (:instance natnum-countable-thm (num (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                                         (* 2 (acl2-pi)))))
                 (:instance k-range-3 (n n) (x (mod (* n angle) (* 2 (acl2-pi)))) (angle angle)
                            (k (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                  (* 2 (acl2-pi)))))
                 (:instance integerp-r-mod-r-x/x (r (* n angle)) (x (* 2 (acl2-pi))))
                 (:instance realnum-equiv (r (* n angle)) (x (* 2 (acl2-pi))))
                 (:instance posp-countable-thm (num n))
                 (:instance exists-angle>=0<2pi-suff (p1 p1) (p2 p2) (angle (mod (* n angle) (* 2 (acl2-pi)))))
                 (:instance range-mod-r-x (r (* n angle)) (x (* 2 (acl2-pi))))
                 (:instance angles-countable-1)
                 (:instance angles-countable-2)
                 (:instance angles-countable-8 (p1 p1) (p2 p2)
                            (p3 (rotation-3d (mod (* n angle) (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (witp1 (pole-seq (nth-pole-exists-witness p1)))
                            (witp2 (pole-seq (nth-pole-exists-witness p2))))
                 (:instance r-theta1*p=p-r-theta2*p=p=>1=2-d-p
                            (angle1 (mod (* n angle) (* 2 (acl2-pi))))
                            (angle2 (exists-angle>=0<2pi-witness p1 p2))
                            (u (point-on-s2-not-d))
                            (p p1))
                 (:instance r-theta1*p=p-r-theta2*p=p=>1=2-d-p
                            (angle1 (exists-angle>=0<2pi-witness p1 p2))
                            (angle2 (exists-angle>=0<2pi-witness (pole-seq (nth-pole-exists-witness p1))
                                                                 (pole-seq (nth-pole-exists-witness p2))))
                            (u (point-on-s2-not-d))
                            (p p1))
                 (:instance angles-countable-11)
                 (:instance rotation-angle=2pik
                            (k (* (+ (* n angle)
                                     (- (mod (* n angle) (* 2 (acl2-pi)))))
                                  (/ (* 2 (acl2-pi)))))
                            (x (mod (* n angle) (* 2 (acl2-pi))))
                            (u (point-on-s2-not-d)))
                 (:instance angles-countable-3)
                 (:instance angles-countable-5)
                 (:instance angles-countable-7)
                 (:instance angles-countable-9)
                 (:instance angles-countable-12)
                 (:instance angles-countable-4 (p (* (+ (* n angle)
                                                        (- (mod (* n angle) (* 2 (acl2-pi)))))
                                                     (/ (* 2 (acl2-pi))))))
                 (:instance angles-countable-6 (p (* (+ (* n angle)
                                                        (- (mod (* n angle) (* 2 (acl2-pi)))))
                                                     (/ (* 2 (acl2-pi))))))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance exists-angle>=0<2pi-suff
                            (angle (exists-angle>=0<2pi-witness p1 p2))
                            (p1 (pole-seq (nth-pole-exists-witness p1)))
                            (p2 (pole-seq (nth-pole-exists-witness p2))))
                 (:instance exists-angle>=0<2pi
                            (p1 (pole-seq (nth-pole-exists-witness p1)))
                            (p2 (pole-seq (nth-pole-exists-witness p2))))
                 (:instance angles-countable-10
                            (y (rotation-3d (exists-angle>=0<2pi-witness
                                             (pole-seq (nth-pole-exists-witness p1))
                                             (pole-seq (nth-pole-exists-witness p2)))
                                            (point-on-s2-not-d)))
                            (x (rotation-3d (exists-angle>=0<2pi-witness p1 p2)
                                            (point-on-s2-not-d)))
                            (p1 p1)
                            (p2 p2)
                            (witp1 (pole-seq (nth-pole-exists-witness p1)))
                            (witp2 (pole-seq (nth-pole-exists-witness p2))))
                 (:instance angles-countable-thm
                            (n1 (nth-pole-exists-witness p1))
                            (n2 (nth-pole-exists-witness p2))
                            (n3 (num>=0-exists-witness (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                                          (* 2 (acl2-pi)))))
                            (n4 (num>=1-exists-witness n))
                            (p1 (pole-seq (nth-pole-exists-witness p1)))
                            (p2 (pole-seq (nth-pole-exists-witness p2)))
                            (nat (/ (- (* n angle) (mod (* n angle) (* 2 (acl2-pi))))
                                    (* 2 (acl2-pi))))
                            (pos n)
                            (angle (mod (* n angle) (* 2 (acl2-pi))))))
           :in-theory nil
           ))
  )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthm p1p2-n-p-seq-lemma*1/2.2-1
   (implies (and (not (zp n))
		 (not (posp (+ -1 n)))
		 (posp n))
	    (equal n 1))
   :rule-classes nil)

 (defthmd p1p2-n-p-seq-lemma*1/2.2-2
   (implies (and (not (zp n))
		 (not (posp (+ -1 n)))
		 (posp n))
	    (equal (nth (+ -1 n) (p1p2-n-p-seq n))
		   (nth 0 (p1p2-n-p-seq-i n)))))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd p1p2-n-p-seq-lemma-1
   (implies (posp n)
	    (realp (cadar (p1p2-n-p-seq-i n)))))

 (defthmd p1p2-n-p-seq-2-len
   (implies (natp n)
	    (equal (len (p1p2-n-p-seq-2 n)) n)))
 )

(defthmd p1p2-n-p-seq-lemma-2
  (implies (and (posp n)
                (equal (append a b) c)
                (equal (len a) (- n 1)))
           (equal (nth (- n 1) c)
                  (nth 0 b))))

(defthmd p1p2-n-p-seq-lemma-3
  (implies (posp n)
           (equal (p1p2-n-p-seq-2 n)
                  (append (p1p2-n-p-seq-2 (- n 1)) (p1p2-n-p-seq-i n))))
  :hints (("goal"
           :in-theory (disable p1p2-n-p-seq-i)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd p1p2-n-p-seq-lemma
   (implies (posp n)
	    (equal (nth (- n 1) (p1p2-n-p-seq n))
		   (nth 0 (p1p2-n-p-seq-i n))))
   :hints (("goal"
	    :in-theory (disable p1p2-n-p-seq-i)
	    :induct (p1p2-n-p-seq-2 n)
	    )
	   ("subgoal *1/2"
	    :in-theory nil
	    )
	   ("subgoal *1/2.1"
	    :use ((:instance p1p2-n-p-seq-lemma-2 (n n)
			     (a (p1p2-n-p-seq-2 (- n 1)))
			     (b (p1p2-n-p-seq-i n))
			     (c (p1p2-n-p-seq-2 n)))
		  (:instance p1p2-n-p-seq-2-len (n (- n 1)))
		  (:instance p1p2-n-p-seq-lemma-3
			     (n n)))
	    :in-theory (e/d (p1p2-n-p-seq natp) (p1p2-n-p-seq-i))
	    )
	   ("subgoal *1/2.2"
	    :use (:instance p1p2-n-p-seq-lemma*1/2.2-2)
	    )
	   ))
 )

(defthmd realp-pos-p1p2-n-p-sequence
  (implies (posp n)
           (realp (cadr (p1p2-n-p-sequence n))))
  :hints (("goal"
           :use ((:instance p1p2-n-p-seq-lemma (n n))
                 (:instance p1p2-n-p-seq-lemma-1 (n n)))
           :in-theory (disable p1p2-n-p-seq-i)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthm p1p2-n-seq-lemma*1/2.2-1
   (implies (and (not (zp n))
		 (not (posp (+ -1 n)))
		 (posp n))
	    (equal n 1))
   :rule-classes nil)

 (defthmd p1p2-n-seq-lemma*1/2.2-2
   (implies (and (not (zp n))
		 (not (posp (+ -1 n)))
		 (posp n))
	    (equal (nth (+ -1 n) (p1p2-n-seq n))
		   (nth 0 (p1p2-n-seq-i n)))))
 )

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd p1p2-n-seq-lemma-1
   (implies (posp n)
	    (realp (cadar (p1p2-n-seq-i n)))))

 (defthmd p1p2-n-seq-2-len
   (implies (natp n)
	    (equal (len (p1p2-n-seq-2 n)) n)))
 )

(defthmd p1p2-n-seq-lemma-3
  (implies (posp n)
           (equal (p1p2-n-seq-2 n)
                  (append (p1p2-n-seq-2 (- n 1)) (p1p2-n-seq-i n))))
  :hints (("goal"
           :in-theory (disable p1p2-n-seq-i)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd p1p2-n-seq-lemma
   (implies (posp n)
	    (equal (nth (- n 1) (p1p2-n-seq n))
		   (nth 0 (p1p2-n-seq-i n))))
   :hints (("goal"
	    :in-theory (disable p1p2-n-seq-i)
	    :induct (p1p2-n-seq-2 n)
	    )
	   ("subgoal *1/2"
	    :in-theory nil
	    )
	   ("subgoal *1/2.1"
	    :use ((:instance p1p2-n-p-seq-lemma-2 (n n)
			     (a (p1p2-n-seq-2 (- n 1)))
			     (b (p1p2-n-seq-i n))
			     (c (p1p2-n-seq-2 n)))
		  (:instance p1p2-n-seq-2-len (n (- n 1)))
		  (:instance p1p2-n-seq-lemma-3
			     (n n)))
	    :in-theory (e/d (p1p2-n-seq natp) (p1p2-n-seq-i))
	    )
	   ("subgoal *1/2.2"
	    :use (:instance p1p2-n-seq-lemma*1/2.2-2)
	    )
	   ))
 )

(defthmd realp-nat-p1p2-n-sequence
  (implies (posp n)
           (realp (cadr (p1p2-n-sequence n))))
  :hints (("goal"
           :use ((:instance p1p2-n-seq-lemma (n n))
                 (:instance p1p2-n-seq-lemma-1 (n n)))
           :in-theory (disable p1p2-n-seq-i)
           )))

(defthmd realp-natp-p1p2-n-p-sequence-1
  (implies (realp (cadar (nth 0 (p1p2-n-p-seq-i n))))
           (realp (cadar (p1p2-n-p-sequence n))))
  :hints (("goal"
           :use ((:instance p1p2-n-p-seq-lemma (n n)))
           :in-theory (disable p1p2-n-p-seq-i)
           )))

(defthmd realp-natp-p1p2-n-p-sequence-2
  (implies (posp n)
           (equal (cadar (nth 0 (p1p2-n-p-seq-i n)))
                  (car (cdr (p1p2-n-sequence (nth 0 (mod-remainder-2 0 n)))))))
  :hints (("goal"
           :in-theory (disable mod-remainder-2 mod-remainder-3)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd pip2-n-p-sequence-pos-realp
   (realp (cadr (p1p2-n-p-sequence n)))
   :hints (("goal"
	    :use ((:instance realp-pos-p1p2-n-p-sequence (n n)))
	    :in-theory (disable p1p2-n-seq p1p2-n-p-seq p1p2-n-p-seq-i p1p2-n-seq-i mod-remainder-2)
	    ))))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd pip2-n-p-sequence-nat-realp
   (realp (cadar (p1p2-n-p-sequence n)))
   :hints (("goal"
	    :use ((:instance realp-natp-p1p2-n-p-sequence-1 (n n))
		  (:instance realp-natp-p1p2-n-p-sequence-2 (n n))
		  (:instance realp-nat-p1p2-n-sequence (n (nth 0 (mod-remainder-2 0 n)))))
	    :in-theory (disable p1p2-n-seq p1p2-n-p-seq p1p2-n-p-seq-i p1p2-n-seq-i mod-remainder-2)
	    ))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthmd angle-sequence-realp
   (realp (angles-seq n))
   :hints (("goal"
	    :use ((:instance angles-countable-thm-2 (n n) (q (- n 1)))
		  (:instance pip2-n-p-sequence-pos-realp)
		  (:instance pip2-n-p-sequence-nat-realp)
		  (:instance generate-angles-lemma1 (n (- n 1)))
		  (:instance generate-angles-lemma1 (n n)))
	    :in-theory (disable generate-angles p1p2-n-p-sequence exists-angle>=0<2pi)
	    )
	   ("subgoal 2"
	    :cases ((exists-angle>=0<2pi (car (car (car (p1p2-n-p-sequence n))))
					 (cadr (car (car (p1p2-n-p-sequence n)))))))
	   ("subgoal 2.1"
	    :use ((:instance angles-countable-9 (p1 (car (car (car (p1p2-n-p-sequence n)))))
			     (p2 (cadr (car (car (p1p2-n-p-sequence n)))))))
	    )
	   ))
 )

(defun-sk exists-in-interval-but-not-in-angle-sequence (a b)
  (exists angle
          (and (realp angle)
               (< a angle)
               (< angle b)
               (not (nth-angle-exists angle)))))

(encapsulate
 ()

 (local (include-book "nonstd/transcendentals/reals-are-uncountable-1" :dir :system))

 (defthmd existence-of-angle-not-in-sequence
   (exists-in-interval-but-not-in-angle-sequence 0 (* 2 (acl2-pi)))
   :hints (("goal"
	    :use ((:functional-instance reals-are-not-countable
					(seq angles-seq)
					(a (lambda () 0))
					(b (lambda () (* 2 (acl2-pi))))
					(exists-in-sequence nth-angle-exists)
					(exists-in-sequence-witness nth-angle-exists-witness)
					(exists-in-interval-but-not-in-sequence exists-in-interval-but-not-in-angle-sequence)
					(exists-in-interval-but-not-in-sequence-witness exists-in-interval-but-not-in-angle-sequence-witness)))
	    )
	   ("subgoal 4"
	    :use (
		  (:instance exists-in-interval-but-not-in-angle-sequence-suff (angle x))
		  )
	    )
	   ("subgoal 3"
	    :in-theory (disable nth-angle-exists)
	    )
	   ("subgoal 2"
	    :use (:instance nth-angle-exists-suff (n i) (angle x))
	    :in-theory (disable angles-seq)
	    )
	   ("subgoal 1"
	    :in-theory (disable angles-seq)
	    )
	   ))
 )

(defthmd witness-not-in-angle-sequence
  (and (realp (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
       (<= 0 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
       (< (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (* 2 (acl2-pi)))
       (not (nth-angle-exists (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
  :hints (("goal"
           :use ((:instance existence-of-angle-not-in-sequence))
           )))

(defthmd rot-angle-witness*p1!=p2
  (implies (and (d-p p1)
                (d-p p2)
                (posp n))
           (not (m-= (m-* (rotation-3d (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                       (point-on-s2-not-d)) p1) p2)))
  :hints (("goal"
           :use ((:instance witness-not-in-angle-sequence)
                 (:instance angles-countable (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                            (p1 p1)
                            (p2 p2)
                            (n n)))
           )))

(defthmd rot-angle-witness*p1!=p2-intmn-1
  (implies (m-= m n)
           (m-= (m-* p m) (m-* p n))))

(defthmd rot-angle-witness*p1!=p2-intmn-2
  (implies (and (integerp m)
                (posp n))
           (realp (* (+ m n)
                     (exists-in-interval-but-not-in-angle-sequence-witness
                      0 (* 2 (acl2-pi))))))
  :hints (("goal"
           :use ((:instance witness-not-in-angle-sequence))
           )))

(defthmd rot-angle-witness*p1!=p2-intmn-3
  (equal (m-* p (m-* m1 m2))
         (m-* (m-* p m1) m2)))

(defthmd rot-angle-witness*p1!=p2-intmn-4
  (implies (m-= x y)
           (m-= (m-* x p1) (m-* y p1))))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd rot-angle-witness*p1!=p2-intmn-5
   (equal (rotation-3d (+ (* (- m)
			     (exists-in-interval-but-not-in-angle-sequence-witness
			      0 (* 2 (acl2-pi))))
			  (* (+ m n)
			     (exists-in-interval-but-not-in-angle-sequence-witness
			      0 (* 2 (acl2-pi)))))
		       (point-on-s2-not-d))
	  (rotation-3d (* n
			  (exists-in-interval-but-not-in-angle-sequence-witness
			   0 (* 2 (acl2-pi))))
		       (point-on-s2-not-d)))
   :hints (("goal"
	    :in-theory (disable rotation-3d)
	    )))
 )


(defthmd rot-angle-witness*p1!=p2-intmn-6
  (implies (and (d-p p1)
                (d-p p2)
                (integerp m)
                (posp n))
           (m-= (m-*
                 (rotation-3d (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                 (m-* (rotation-3d (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                      p1))
                (m-* (rotation-3d (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p1)))
  :hints (("goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-3
                            (p (rotation-3d (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (m1 (rotation-3d (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (m2 p1))
                 (:instance rot-angle-witness*p1!=p2-intmn-5)
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                            (angle2 (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance rot-angle-witness*p1!=p2-intmn-2 (m m) (n n))
                 (:instance rot-angle-witness*p1!=p2-intmn-4
                            (x (m-* (rotation-3d (* (- m)
                                                    (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (rotation-3d (* (+ m n)
                                                    (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))))
                            (y (rotation-3d (+ (* (- m)
                                                  (exists-in-interval-but-not-in-angle-sequence-witness
                                                   0 (* 2 (acl2-pi))))
                                               (* (+ m n)
                                                  (exists-in-interval-but-not-in-angle-sequence-witness
                                                   0 (* 2 (acl2-pi)))))
                                            (point-on-s2-not-d)))
                            (p1 p1))
                 )
           :in-theory nil
           )))

(defthmd rot-angle-witness*p1!=p2-intmn-7
  (implies (and (m-= x y)
                (m-= y p2))
           (m-= x p2)))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))
 (defthmd rot-angle-witness*p1!=p2-intmn-8
   (equal
    (rotation-3d (+ (* (- m)
		       (exists-in-interval-but-not-in-angle-sequence-witness
			0 (* 2 (acl2-pi))))
		    (* m
		       (exists-in-interval-but-not-in-angle-sequence-witness
			0 (* 2 (acl2-pi)))))
		 (point-on-s2-not-d))
    (rotation-3d 0 (point-on-s2-not-d))))
 )

(defthmd rot-angle-witness*p1!=p2-intmn-9
  (implies (and (d-p p1)
                (d-p p2)
                (integerp m)
                (posp n))
           (m-= (m-*
                 (rotation-3d (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                 (m-* (rotation-3d (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                      p2))
                p2))
  :hints (("goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-3
                            (p (rotation-3d (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (m1 (rotation-3d (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (m2 p2))
                 (:instance rot-angle-witness*p1!=p2-intmn-7 (x (m-* (m-* (rotation-3d (* (- m)
                                                                                          (exists-in-interval-but-not-in-angle-sequence-witness
                                                                                           0 (* 2 (acl2-pi))))
                                                                                       (point-on-s2-not-d))
                                                                          (rotation-3d (* m
                                                                                          (exists-in-interval-but-not-in-angle-sequence-witness
                                                                                           0 (* 2 (acl2-pi))))
                                                                                       (point-on-s2-not-d)))
                                                                     p2))
                            (y (m-* (rotation-3d (+ (* (- m)
                                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                                        0 (* 2 (acl2-pi))))
                                                    (* m
                                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                                        0 (* 2 (acl2-pi)))))
                                                 (point-on-s2-not-d))
                                    p2))
                            (p2 p2))
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                            (angle2 (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance rot-angle-witness*p1!=p2-intmn-4
                            (x (m-* (rotation-3d (* (- m)
                                                    (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (rotation-3d (* m
                                                    (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))))
                            (y (rotation-3d (+ (* (- m)
                                                  (exists-in-interval-but-not-in-angle-sequence-witness
                                                   0 (* 2 (acl2-pi))))
                                               (* m
                                                  (exists-in-interval-but-not-in-angle-sequence-witness
                                                   0 (* 2 (acl2-pi)))))
                                            (point-on-s2-not-d)))
                            (p1 p2))
                 (:instance rot-angle-witness*p1!=p2-intmn-8)
                 (:instance rotation-a-witn-of0 (u (point-on-s2-not-d)) (p p2))
                 (:instance d-p (point p2))
                 (:instance s2-def-p (point p2))
                 )
           :in-theory nil
           )))

(defthmd rot-angle-witness*p1!=p2-intmn
  (implies (and (d-p p1)
                (d-p p2)
                (integerp m)
                (posp n))
           (not (m-= (m-*
                      (rotation-3d (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                      p1)
                     (m-* (rotation-3d (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p2))))
  :hints (("goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-1
                            (m (m-* (rotation-3d (* (+ m n) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p1))
                            (p (rotation-3d (* (- m) (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)))
                            (n (rotation-3d (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance rot-angle-witness*p1!=p2 (p1 p1) (p2 p2) (n n))
                 (:instance rot-angle-witness*p1!=p2-intmn-9)
                 (:instance rot-angle-witness*p1!=p2-intmn-6)
                 )
           :in-theory (disable m-= d-p m-* nth-angle-exists rotation-3d point-in-r3 aref2 point-on-s2-not-d)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd rot-angle-witness*p1!=p2-pospmn
   (implies (and (d-p p1)
		 (d-p p2)
		 (posp m)
		 (< m n)
		 (posp n))
	    (not (m-= (m-*
		       (rotation-3d (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
		       p1)
		      (m-* (rotation-3d (* m (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p2))))
   :hints (("goal"
	    :use ((:instance rot-angle-witness*p1!=p2-intmn (p1 p1) (p2 p2) (m m) (n (- n m))))
	    :in-theory (disable m-= d-p m-* nth-angle-exists rotation-3d point-in-r3 aref2 point-on-s2-not-d)
	    )))
 )

(defun-sk exists-d-p (n point)
  (exists p
          (and (d-p p)
               (m-= (m-* (rotation-3d
                          (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                          (point-on-s2-not-d))
                         p)
                    point))))

(defthmd exists-d-p=>
  (implies (exists-d-p n point)
           (and (d-p (exists-d-p-witness n point))
                (m-= (m-* (rotation-3d
                           (* n (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                           (point-on-s2-not-d))
                          (exists-d-p-witness n point))
                     point)))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-3d)
           )))

(defun-sk efunc (point)
  (exists n
          (and (natp n)
               (exists-d-p n point))))

(defthmd efunc=>
  (implies (efunc point)
           (and (m-= (m-* (rotation-3d
                           (* (efunc-witness point)
                              (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                           (point-on-s2-not-d))
                          (exists-d-p-witness (efunc-witness point) point))
                     point)
                (natp (efunc-witness point))
                (d-p (exists-d-p-witness (efunc-witness point) point))))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-3d)
           )))

(defun set-e-p (point)
  (and (point-in-r3 point)
       (efunc point)))

(defun-sk seq-witness*e-func (point)
  (exists p
          (and (set-e-p p)
               (m-= (m-* (rotation-3d
                          (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                          (point-on-s2-not-d))
                         p)
                    point))))

(defthmd seq-witness*e-func=>
  (implies (seq-witness*e-func point)
           (and (set-e-p (seq-witness*e-func-witness point))
                (m-= (m-* (rotation-3d
                           (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                           (point-on-s2-not-d))
                          (seq-witness*e-func-witness point))
                     point)))
  :hints (("goal"
           :in-theory (disable d-p point-on-s2-not-d rotation-3d efunc)
           )))

(defun rot-witness*e-func (point)
  (and (point-in-r3 point)
       (seq-witness*e-func point)))

(defun efunc-not-d (point)
  (and (set-e-p point)
       (not (d-p point))))

(defthmd seq-witness*e-func=>enotd-1
  (implies (natp n)
           (natp (+ n 1))))

(defthmd seq-witness*e-func=>enotd-2
  (implies (and (m-= (m-* rn1 y) z)
                (m-= (m-* r1 z) point))
           (m-= (m-* (m-* r1 rn1) y) point)))

(defthmd seq-witness*e-func=>enotd-3
  (implies (and (natp n)
                (realp x))
           (realp (* n x))))

(defthmd rot-witness*e-func=>e
  (implies (rot-witness*e-func point)
           (set-e-p point))
  :hints (("goal"
           :use ((:instance seq-witness*e-func=> (point point))
                 (:instance efunc=> (point (seq-witness*e-func-witness point)))
                 (:instance exists-d-p-suff
                            (n (+ (efunc-witness (seq-witness*e-func-witness point)) 1))
                            (point point)
                            (p (exists-d-p-witness
                                (efunc-witness (seq-witness*e-func-witness point))
                                (seq-witness*e-func-witness point))))
                 (:instance efunc-suff (point point) (n (+ (efunc-witness (seq-witness*e-func-witness point)) 1)))
                 (:instance seq-witness*e-func=>enotd-1
                            (n (efunc-witness (seq-witness*e-func-witness point))))
                 (:instance seq-witness*e-func=>enotd-2
                            (rn1 (rotation-3d
                                  (* (efunc-witness (seq-witness*e-func-witness point))
                                     (exists-in-interval-but-not-in-angle-sequence-witness
                                      0 (* 2 (acl2-pi))))
                                  (point-on-s2-not-d)))
                            (y (exists-d-p-witness (efunc-witness (seq-witness*e-func-witness point))
                                                   (seq-witness*e-func-witness point)))
                            (z (seq-witness*e-func-witness point))
                            (r1 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (point point))
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                            (angle2 (* (efunc-witness (seq-witness*e-func-witness point))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance seq-witness*e-func=>enotd-3
                            (n (efunc-witness (seq-witness*e-func-witness point)))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 )
           :in-theory (disable rotation-3d d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
                               point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
                               nth-angle-exists)
           )))

(defthmd rot-witness*e-func=>notd
  (implies (rot-witness*e-func point)
           (not (d-p point)))
  :hints (("goal"
           :use ((:instance seq-witness*e-func=> (point point))
                 (:instance efunc=> (point (seq-witness*e-func-witness point)))
                 (:instance exists-d-p-suff
                            (n (+ (efunc-witness (seq-witness*e-func-witness point)) 1))
                            (point point)
                            (p (exists-d-p-witness
                                (efunc-witness (seq-witness*e-func-witness point))
                                (seq-witness*e-func-witness point))))
                 (:instance seq-witness*e-func=>enotd-1
                            (n (efunc-witness (seq-witness*e-func-witness point))))
                 (:instance seq-witness*e-func=>enotd-2
                            (rn1 (rotation-3d
                                  (* (efunc-witness (seq-witness*e-func-witness point))
                                     (exists-in-interval-but-not-in-angle-sequence-witness
                                      0 (* 2 (acl2-pi))))
                                  (point-on-s2-not-d)))
                            (y (exists-d-p-witness (efunc-witness (seq-witness*e-func-witness point))
                                                   (seq-witness*e-func-witness point)))
                            (z (seq-witness*e-func-witness point))
                            (r1 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (point point))
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                            (angle2 (* (efunc-witness (seq-witness*e-func-witness point))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance seq-witness*e-func=>enotd-3
                            (n (efunc-witness (seq-witness*e-func-witness point)))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance rot-angle-witness*p1!=p2
                            (p1 (exists-d-p-witness (efunc-witness (seq-witness*e-func-witness point))
                                                    (seq-witness*e-func-witness point)))
                            (p2 point)
                            (n (+ (efunc-witness (seq-witness*e-func-witness point))
                                  1)))
                 )
           :in-theory (disable rotation-3d d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
                               point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
                               nth-angle-exists)
           )))

(defthmd rot-witness*e-func=>efunc-not-d
  (implies (rot-witness*e-func point)
           (efunc-not-d point))
  :hints (("goal"
           :use ((:instance rot-witness*e-func=>e)
                 (:instance rot-witness*e-func=>notd))
           :in-theory (disable rotation-3d d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
                               point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
                               nth-angle-exists)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd efunc-not-d=>rot-witness*e-func-1
   (implies (efunc-not-d point)
	    (posp (efunc-witness point)))
   :hints (("goal"
	    :use ((:instance efunc=> (point point))
		  (:instance diff-d-p-p=>d-p-p1 (p (exists-d-p-witness (efunc-witness point) point))
			     (p1 point))
		  (:instance rotation-a-witn-of0 (p (exists-d-p-witness (efunc-witness point) point))
			     (u (point-on-s2-not-d)))
		  (:instance exists-point-on-s2-not-d-2)
		  (:instance s2-def-p (point (point-on-s2-not-d)))
		  (:instance efunc-not-d (point point))
		  (:instance d-p (point (exists-d-p-witness (efunc-witness point) point)))
		  (:instance s2-def-p (point (exists-d-p-witness (efunc-witness point) point)))
		  )
	    :in-theory (disable rotation-3d d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
				point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
				nth-angle-exists exists-d-p m-=)
	    )))
 )

(defthmd efunc-not-d=>rot-witness*e-func-2-1
  (implies (posp n)
           (natp (- n 1))))

(defthmd efunc-not-d=>rot-witness*e-func-2
  (implies (efunc-not-d point)
           (efunc (m-* (rotation-3d (* (+ -1 (efunc-witness point))
                                       (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi))))
                                    (point-on-s2-not-d))
                       (exists-d-p-witness (efunc-witness point) point))))
  :hints (("goal"
           :use ((:instance efunc=> (point point))
                 (:instance set-e-p (point point))
                 (:instance efunc-not-d=>rot-witness*e-func-1 (point point))
                 (:instance exists-d-p-suff
                            (point (m-* (rotation-3d (* (+ -1 (efunc-witness point))
                                                        (exists-in-interval-but-not-in-angle-sequence-witness
                                                         0 (* 2 (acl2-pi))))
                                                     (point-on-s2-not-d))
                                        (exists-d-p-witness (efunc-witness point) point)))
                            (p (exists-d-p-witness (efunc-witness point) point))
                            (n (+ -1 (efunc-witness point))))
                 (:instance efunc-suff
                            (point (m-* (rotation-3d (* (+ -1 (efunc-witness point))
                                                        (exists-in-interval-but-not-in-angle-sequence-witness
                                                         0 (* 2 (acl2-pi))))
                                                     (point-on-s2-not-d))
                                        (exists-d-p-witness (efunc-witness point) point)))
                            (n (+ -1 (efunc-witness point))))
                 (:instance efunc-not-d=>rot-witness*e-func-2-1
                            (n (efunc-witness point)))
                 (:instance efunc-not-d (point point)))
           :in-theory nil
           )))

(defthmd efunc-not-d=>rot-witness*e-func-3-1
  (equal (m-* a b c)
         (m-* (m-* a b) c)))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd efunc-not-d=>rot-witness*e-func-3
   (implies (and (efunc point)
		 (point-in-r3 point)
		 (realp (* (+ -1 (efunc-witness point))
			   (exists-in-interval-but-not-in-angle-sequence-witness
			    0 (* 2 (acl2-pi)))))
		 (not (d-p point)))
	    (rot-witness*e-func point))
   :hints (("goal"
	    :use ((:instance efunc-not-d=>rot-witness*e-func-3-1
			     (a (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
					      0 (* 2 (acl2-pi)))
					     (point-on-s2-not-d)))
			     (b (rotation-3d (* (+ -1 (efunc-witness point))
						(exists-in-interval-but-not-in-angle-sequence-witness
						 0 (* 2 (acl2-pi))))
					     (point-on-s2-not-d)))
			     (c (exists-d-p-witness (efunc-witness point)
						    point)))
		  (:instance seq-witness*e-func-suff
			     (p (m-* (rotation-3d (* (+ -1 (efunc-witness point))
						     (exists-in-interval-but-not-in-angle-sequence-witness
						      0 (* 2 (acl2-pi))))
						  (point-on-s2-not-d))
				     (exists-d-p-witness (efunc-witness point) point)))
			     (point point))
		  (:instance rot-witness*e-func (point point))
		  (:instance efunc-not-d (point point))
		  (:instance efunc-not-d=>rot-witness*e-func-2 (point point))
		  (:instance efunc=> (point point))
		  (:instance r-t1*r-t2=r-t1+t2
			     (angle1 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
			     (angle2 (* (+ -1 (efunc-witness point))
					(exists-in-interval-but-not-in-angle-sequence-witness
					 0 (* 2 (acl2-pi)))))
			     (u (point-on-s2-not-d)))
		  (:instance rot*p-on-s2 (p (exists-d-p-witness (efunc-witness point) point))
			     (rot (rotation-3d (* (+ -1 (efunc-witness point))
						  (exists-in-interval-but-not-in-angle-sequence-witness
						   0 (* 2 (acl2-pi))))
					       (point-on-s2-not-d))))
		  (:instance s2-def-p (point (m-* (rotation-3d (* (+ -1 (efunc-witness point))
								  (exists-in-interval-but-not-in-angle-sequence-witness
								   0 (* 2 (acl2-pi))))
							       (point-on-s2-not-d))
						  (exists-d-p-witness (efunc-witness point)
								      point))))
		  (:instance d-p (point (exists-d-p-witness (efunc-witness point) point)))
		  (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
		  (:instance exists-point-on-s2-not-d-2)
		  (:instance s2-def-p (point (point-on-s2-not-d)))
		  (:instance witness-not-in-angle-sequence)
		  (:instance set-e-p (point (m-* (rotation-3d (* (+ -1 (efunc-witness point))
								 (exists-in-interval-but-not-in-angle-sequence-witness
								  0 (* 2 (acl2-pi))))
							      (point-on-s2-not-d))
						 (exists-d-p-witness (efunc-witness point)
								     point))))
		  (:instance r3-rotationp-r-theta (angle (* (+ -1 (efunc-witness point))
							    (exists-in-interval-but-not-in-angle-sequence-witness
							     0 (* 2 (acl2-pi))))))
		  )
	    :in-theory(disable rotation-3d d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
			       point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
			       nth-angle-exists exists-d-p m-= r3-rotationp)
	    )))

 (defthmd efunc-not-d=>rot-witness*e-func
   (implies (efunc-not-d point)
	    (rot-witness*e-func point))
   :hints (("goal"
	    :use ((:instance efunc-not-d=>rot-witness*e-func-3 (point point))
		  (:instance efunc=> (point point))
		  (:instance witness-not-in-angle-sequence))
	    :in-theory (disable efunc d-p rot-witness*e-func point-in-r3)
	    )))
 )

(defthmd efunc-not-d-iff-rot-witness*e-func
  (iff (efunc-not-d point)
       (rot-witness*e-func point))
  :hints (("goal"
           :use ((:instance efunc-not-d=>rot-witness*e-func)
                 (:instance rot-witness*e-func=>efunc-not-d))
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd d-p=>set-e
   (implies (d-p point)
	    (set-e-p point))
   :hints (("goal"
	    :use ((:instance set-e-p (point point))
		  (:instance efunc-suff (point point) (n 0))
		  (:instance d-p (point point))
		  (:instance s2-def-p (point point))
		  (:instance rotation-a-witn-of0 (p point)
			     (u (point-on-s2-not-d)))
		  (:instance exists-point-on-s2-not-d-2)
		  (:instance s2-def-p (point (point-on-s2-not-d)))
		  (:instance exists-d-p-suff (point point) (n 0) (p point)))
	    :in-theory(disable rotation-3d d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func
			       point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 m-= s2-def-p
			       nth-angle-exists exists-d-p m-= r3-rotationp)
	    )))
 )

(defun s2-not-e (point)
  (and (s2-def-p point)
       (not (set-e-p point))))

(defthmd s2-not-e=>s2-not-d
  (implies (s2-not-e point)
           (s2-d-p point))
  :hints (("goal"
           :use ((:instance d-p=>set-e (point point)))
           :in-theory (disable s2-def-p d-p set-e-p)
           )))

(defun s2-not-d-n-s2-not-e (point)
  (and (s2-d-p point)
       (s2-not-e point)))

(defthmd s2-not-e=>s2-not-d-n-s2-not-e
  (iff (s2-not-e point)
       (s2-not-d-n-s2-not-e point))
  :hints (("goal"
           :use ((:instance s2-not-e=>s2-not-d))
           )))

(defun s2-d-p-n-set-e (point)
  (and (s2-d-p point)
       (set-e-p point)))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd set-e-p=>s2-def-p
   (implies (set-e-p point)
	    (s2-def-p point))
   :hints (("goal"
	    :use ((:instance s2-def-p-p=>p1
			     (p (m-* (rotation-3d
				      (* (efunc-witness point)
					 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
				      (point-on-s2-not-d))
				     (exists-d-p-witness (efunc-witness point) point)))
			     (p1 point))
		  (:instance set-e-p (point point))
		  (:instance efunc (point point))
		  (:instance exists-d-p (n (efunc-witness point))
			     (point point))
		  (:instance d-p (point (exists-d-p-witness (efunc-witness point) point)))
		  (:instance rot*p-on-s2 (p (exists-d-p-witness (efunc-witness point) point))
			     (rot (rotation-3d (* (efunc-witness point)
						  (exists-in-interval-but-not-in-angle-sequence-witness
						   0 (* 2 (acl2-pi))))
					       (point-on-s2-not-d))))
		  (:instance r3-rotationp-r-theta (angle (* (efunc-witness point)
							    (exists-in-interval-but-not-in-angle-sequence-witness
							     0 (* 2 (acl2-pi))))))
		  (:instance witness-not-in-angle-sequence)
		  )
	    :in-theory (disable rotation-3d d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 nth-angle-exists exists-d-p m-= r3-rotationp)
	    )))
 )


(defthmd enotd=>s2-d-p-n-set-e
  (iff (efunc-not-d point)
       (s2-d-p-n-set-e point))
  :hints (("goal"
           :use ((:instance s2-d-p (point point))
                 (:instance set-e-p=>s2-def-p (point point)))
           :in-theory (disable set-e-p d-p s2-d-p s2-def-p)
           )))

(defun-sk wit-inv*s2-d-p-n-set-e-1 (point)
  (exists p
          (and (s2-d-p-n-set-e p)
               (m-= (m-* (rotation-3d
                          (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                          (point-on-s2-not-d)) p)
                    point))))

(defun wit-inv*s2-d-p-n-set-e-p (point)
  (and (point-in-r3 point)
       (wit-inv*s2-d-p-n-set-e-1 point)))


(defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
  (implies (and (point-in-r3 p1)
                (r3-matrixp rot))
           (point-in-r3 (m-* rot p1)))
  :hints (("goal"
           :use ((:instance array2p-alist2p (name :fake-name) (l rot))
                 (:instance array2p-alist2p (name :fake-name) (l p1))
                 (:instance aref2-m-* (name :fake-name)
                            (m1 rot) (m2 p1) (i 0) (j 0))
                 (:instance aref2-m-* (name :fake-name)
                            (m1 rot) (m2 p1) (i 1) (j 0))
                 (:instance aref2-m-* (name :fake-name)
                            (m1 rot) (m2 p1) (i 2) (j 0)))
           :in-theory (e/d (m-* array2p header dimensions) (aref2-m-* array2p-alist2p r3-m-determinant r3-m-inverse m-trans))
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1
   (implies (set-e-p point)
	    (wit-inv*s2-d-p-n-set-e-p point))
   :hints (("goal"
	    :use ((:instance wit-inv*s2-d-p-n-set-e-p (point point))
		  (:instance wit-inv*s2-d-p-n-set-e-1-suff
			     (point point)
			     (p (m-* (rotation-3d
				      (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
				      (point-on-s2-not-d)) point)))
		  (:instance enotd=>s2-d-p-n-set-e
			     (point (m-* (rotation-3d
					  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
					  (point-on-s2-not-d)) point)))
		  (:instance efunc-not-d-iff-rot-witness*e-func
			     (point (m-* (rotation-3d
					  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
					  (point-on-s2-not-d)) point)))
		  (:instance rot-witness*e-func
			     (point (m-* (rotation-3d
					  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
					  (point-on-s2-not-d)) point)))
		  (:instance seq-witness*e-func-suff (p point)
			     (point (m-* (rotation-3d
					  (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
					  (point-on-s2-not-d)) point)))
		  (:instance set-e-p (point point))
		  (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
			     (p1 point)
			     (rot (rotation-3d
				   (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
				   (point-on-s2-not-d))))
		  (:instance r3-rotationp-r-theta (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
		  (:instance witness-not-in-angle-sequence)
		  (:instance r-t1*r-t2=r-t1+t2
			     (angle1 (- (exists-in-interval-but-not-in-angle-sequence-witness
					 0 (* 2 (acl2-pi)))))
			     (angle2 (exists-in-interval-but-not-in-angle-sequence-witness
				      0 (* 2 (acl2-pi))))
			     (u (point-on-s2-not-d)))
		  (:instance exists-point-on-s2-not-d-2)
		  (:instance s2-def-p (point (point-on-s2-not-d)))
		  (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
		  (:instance rotation-a-witn-of0 (p point)
			     (u (point-on-s2-not-d)))
		  (:instance r3-rotationp (m (rotation-3d
					      (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
					      (point-on-s2-not-d))))
		  )
	    :in-theory (disable r3-m-determinant r3-matrixp r3-m-inverse
				m-trans rotation-3d d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 nth-angle-exists exists-d-p m-= r3-rotationp)
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-1
   (implies (and (m-= (m-* rn dpp) seq)
		 (m-= (m-* r1 seq) witn)
		 (m-= (m-* r-1 witn) point))
	    (m-= (m-* (m-* r-1 r1) rn dpp) point)))

 (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
   (implies (and (natp n)
		 (realp x))
	    (realp (* n x))))

 (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-3-1
   (implies (and (m-= (m-* r-1 r1) r0)
		 (m-= (m-* (m-* r-1 r1) rnx dpp) point)
		 (m-= (m-* r0 rnx) rnx1))
	    (m-= (m-* rnx1 dpp) point)))

 (defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-3
   (implies
    (and (natp (efunc-witness
		(seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
	 (m-=
	  (m-*
	   (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
				 0 (* 2 (acl2-pi))))
			     (point-on-s2-not-d))
		(rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
			      0 (* 2 (acl2-pi)))
			     (point-on-s2-not-d)))
	   (rotation-3d
	    (*
	     (efunc-witness
	      (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
	     (exists-in-interval-but-not-in-angle-sequence-witness
	      0 (* 2 (acl2-pi))))
	    (point-on-s2-not-d))
	   (exists-d-p-witness
	    (efunc-witness
	     (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
	    (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
	  point))
    (m-= (m-* (rotation-3d
	       (*
		(efunc-witness
		 (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
		(exists-in-interval-but-not-in-angle-sequence-witness
		 0 (* 2 (acl2-pi))))
	       (point-on-s2-not-d))
	      (exists-d-p-witness
	       (efunc-witness
		(seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
	       (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
	 point))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2
			     (angle1 (- (exists-in-interval-but-not-in-angle-sequence-witness
					 0 (* 2 (acl2-pi)))))
			     (angle2 (exists-in-interval-but-not-in-angle-sequence-witness
				      0 (* 2 (acl2-pi))))
			     (u (point-on-s2-not-d)))
		  (:instance r-t1*r-t2=r-t1+t2
			     (angle1 0)
			     (angle2 (*
				      (efunc-witness
				       (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
				      (exists-in-interval-but-not-in-angle-sequence-witness
				       0 (* 2 (acl2-pi)))))
			     (u (point-on-s2-not-d)))
		  (:instance witness-not-in-angle-sequence)
		  (:instance exists-point-on-s2-not-d-2)
		  (:instance s2-def-p (point (point-on-s2-not-d)))
		  (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
		  (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
			     (n (efunc-witness
				 (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
			     (x (exists-in-interval-but-not-in-angle-sequence-witness
				 0 (* 2 (acl2-pi)))))
		  (:instance efunc-not-d=>rot-witness*e-func-3-1
			     (a (rotation-3d 0 (point-on-s2-not-d)))
			     (b (rotation-3d
				 (*
				  (efunc-witness
				   (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
				  (exists-in-interval-but-not-in-angle-sequence-witness
				   0 (* 2 (acl2-pi))))
				 (point-on-s2-not-d)))
			     (c (exists-d-p-witness
				 (efunc-witness
				  (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
				 (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))))
		  (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-3-1
			     (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
						   0 (* 2 (acl2-pi))))
					       (point-on-s2-not-d)))
			     (r1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
					       0 (* 2 (acl2-pi)))
					      (point-on-s2-not-d)))
			     (point point)
			     (r0 (rotation-3d 0 (point-on-s2-not-d)))
			     (rnx (rotation-3d
				   (* (efunc-witness (seq-witness*e-func-witness
						      (wit-inv*s2-d-p-n-set-e-1-witness point)))
				      (exists-in-interval-but-not-in-angle-sequence-witness
				       0 (* 2 (acl2-pi))))
				   (point-on-s2-not-d)))
			     (rnx1 (rotation-3d
				    (* (efunc-witness (seq-witness*e-func-witness
						       (wit-inv*s2-d-p-n-set-e-1-witness point)))
				       (exists-in-interval-but-not-in-angle-sequence-witness
					0 (* 2 (acl2-pi))))
				    (point-on-s2-not-d)))
			     (dpp (exists-d-p-witness
				   (efunc-witness
				    (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
				   (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))))
		  )
	    :in-theory (disable r3-m-determinant r3-matrixp r3-m-inverse m-trans rotation-3d d-p point-on-s2-not-d m-* exists-d-p efunc seq-witness*e-func point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 efunc aref2 nth-angle-exists exists-d-p r3-rotationp efunc-not-d s2-d-p-n-set-e wit-inv*s2-d-p-n-set-e-p wit-inv*s2-d-p-n-set-e-1 rot-witness*e-func seq-witness*e-func set-e-p aref2 s2-def-p aref2))
	   )))

(defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2
  (implies (wit-inv*s2-d-p-n-set-e-p point)
           (set-e-p point))
  :hints (("goal"
           :use ((:instance wit-inv*s2-d-p-n-set-e-p (point point))
                 (:instance wit-inv*s2-d-p-n-set-e-1 (point point))
                 (:instance enotd=>s2-d-p-n-set-e (point (wit-inv*s2-d-p-n-set-e-1-witness point)))
                 (:instance efunc-not-d-iff-rot-witness*e-func (point (wit-inv*s2-d-p-n-set-e-1-witness point)))
                 (:instance rot-witness*e-func (point (wit-inv*s2-d-p-n-set-e-1-witness point)))
                 (:instance seq-witness*e-func (point (wit-inv*s2-d-p-n-set-e-1-witness point)))
                 (:instance set-e-p (point (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                 (:instance efunc=> (point (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-1
                            (rn (rotation-3d
                                 (*
                                  (efunc-witness
                                   (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                  (exists-in-interval-but-not-in-angle-sequence-witness
                                   0 (* 2 (acl2-pi))))
                                 (point-on-s2-not-d)))
                            (dpp (exists-d-p-witness
                                  (efunc-witness
                                   (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                  (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (r1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (point point)
                            (seq (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                            (witn (wit-inv*s2-d-p-n-set-e-1-witness point))
                            )
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 (- (exists-in-interval-but-not-in-angle-sequence-witness
                                        0 (* 2 (acl2-pi)))))
                            (angle2 (exists-in-interval-but-not-in-angle-sequence-witness
                                     0 (* 2 (acl2-pi))))
                            (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance point-on-s2-not-d-on-s2 (u (point-on-s2-not-d)))
                 (:instance witness-not-in-angle-sequence)
                 (:instance set-e-p (point (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                 (:instance r-t1*r-t2=r-t1+t2
                            (angle1 0)
                            (angle2 (*
                                     (efunc-witness
                                      (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                     (exists-in-interval-but-not-in-angle-sequence-witness
                                      0 (* 2 (acl2-pi)))))
                            (u (point-on-s2-not-d)))
                 (:instance efunc-suff (point point)
                            (n (efunc-witness
                                (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                            )
                 (:instance set-e-p (point point))
                 (:instance exists-d-p-suff (n (efunc-witness
                                                (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                            (point point)
                            (p (exists-d-p-witness
                                (efunc-witness
                                 (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))
                                (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point)))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
                            (n (efunc-witness
                                (seq-witness*e-func-witness (wit-inv*s2-d-p-n-set-e-1-witness point))))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness
                                0 (* 2 (acl2-pi)))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-3)
                 )
           :in-theory nil
           ))
  )

(defthmd set-e-p-iff-wit-inv*s2-d-p-n-set-e-p
  (iff (wit-inv*s2-d-p-n-set-e-p point)
       (set-e-p point)))

(defthmd s2-iff-s2-e-or-e
  (iff (s2-def-p point)
       (or (s2-not-e point)
           (set-e-p point))))

(defthmd iff-s2-s2-e-or-witinv*s2-d-n-e
  (iff (s2-def-p point)
       (or (s2-not-d-n-s2-not-e point)
           (wit-inv*s2-d-p-n-set-e-p point)))
  :hints (("goal"
           :use ((:instance s2-not-e=>s2-not-d-n-s2-not-e (point point))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p (point point))
                 (:instance s2-not-e (point point))
                 (:instance s2-iff-s2-e-or-e (point point))
                 )
           :in-theory nil
           )))

(defun m0 (p)
  (and (diff-n-s2-d-p p)
       (s2-not-e p)))

(defun m1 (p)
  (and (diff-n-s2-d-p p)
       (set-e-p p)))

(defun wa-0 (p)
  (and (diff-a-s2-d-p p)
       (s2-not-e p)))

(defun wa-1 (p)
  (and (diff-a-s2-d-p p)
       (set-e-p p)))

(defun wa-inv-0 (p)
  (and (diff-a-inv-s2-d-p p)
       (s2-not-e p)))

(defun wa-inv-1 (p)
  (and (diff-a-inv-s2-d-p p)
       (set-e-p p)))

(defun wb-0 (p)
  (and (diff-b-s2-d-p p)
       (s2-not-e p)))

(defun wb-1 (p)
  (and (diff-b-s2-d-p p)
       (set-e-p p)))

(defun wb-inv-0 (p)
  (and (diff-b-inv-s2-d-p p)
       (s2-not-e p)))

(defun wb-inv-1 (p)
  (and (diff-b-inv-s2-d-p p)
       (set-e-p p)))

(defun-sk r-1*m1-1 (point)
  (exists p
          (and (m1 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*m1 (p)
  (and (point-in-r3 p)
       (r-1*m1-1 p)))

(defun-sk r-1*wa-1-1 (point)
  (exists p
          (and (wa-1 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*wa-1 (p)
  (and (point-in-r3 p)
       (r-1*wa-1-1 p)))

(defun-sk r-1*wa-inv-1-1 (point)
  (exists p
          (and (wa-inv-1 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*wa-inv-1 (p)
  (and (point-in-r3 p)
       (r-1*wa-inv-1-1 p)))

(defun-sk r-1*wb-1-1 (point)
  (exists p
          (and (wb-1 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*wb-1 (p)
  (and (point-in-r3 p)
       (r-1*wb-1-1 p)))

(defun-sk r-1*wb-inv-1-1 (point)
  (exists p
          (and (wb-inv-1 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun r-1*wb-inv-1 (p)
  (and (point-in-r3 p)
       (r-1*wb-inv-1-1 p)))

(defun r-1-diff-s2 (p)
  (or (r-1*m1 p)
      (r-1*wa-1 p)
      (r-1*wa-inv-1 p)
      (r-1*wb-1 p)
      (r-1*wb-inv-1 p)))

(defthmd s2=>r-1-diff-s2
  (implies (wit-inv*s2-d-p-n-set-e-p p)
           (r-1-diff-s2 p))
  :hints (("goal"
           :use ((:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 (:instance wit-inv*s2-d-p-n-set-e-1 (point p))
                 (:instance s2-d-p-n-set-e (point (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance set-e-p (point (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*m1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance m1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*m1 (p p))
                 (:instance r-1-diff-s2 (p p))
                 (:instance r-1*wa-1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance wa-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*wa-1 (p p))
                 (:instance r-1*wb-1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance wb-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-inv-1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance wb-inv-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*wb-inv-1 (p p))
                 (:instance r-1*wa-inv-1-1-suff (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance wa-inv-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1*wa-inv-1 (p p))
                 )
           :in-theory nil
           )))

(defthmd r-1-diff-s2=>s2
  (implies (r-1-diff-s2 p)
           (wit-inv*s2-d-p-n-set-e-p p))
  :hints (("goal"
           :use ((:instance r-1-diff-s2 (p p))
                 (:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 )
           :cases ((r-1*m1 p)
                   (r-1*wb-inv-1 p)
                   (r-1*wa-inv-1 p)
                   (r-1*wa-1 p)
                   (r-1*wb-1 p))
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance r-1*m1 (p p))
                 (:instance r-1*m1-1 (point p))
                 (:instance m1 (p (r-1*m1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*m1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*m1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*m1-1-witness p)))
                 )
           )
          ("subgoal 4"
           :use ((:instance r-1*wb-inv-1 (p p))
                 (:instance r-1*wb-inv-1-1 (point p))
                 (:instance wb-inv-1 (p (r-1*wb-inv-1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*wb-inv-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*wb-inv-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wb-inv-1-1-witness p)))
                 )
           )
          ("subgoal 3"
           :use ((:instance r-1*wa-inv-1 (p p))
                 (:instance r-1*wa-inv-1-1 (point p))
                 (:instance wa-inv-1 (p (r-1*wa-inv-1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*wa-inv-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*wa-inv-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wa-inv-1-1-witness p)))
                 )
           )
          ("subgoal 2"
           :use ((:instance r-1*wa-1 (p p))
                 (:instance r-1*wa-1-1 (point p))
                 (:instance wa-1 (p (r-1*wa-1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*wa-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*wa-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wa-1-1-witness p)))
                 )
           )
          ("subgoal 1"
           :use ((:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-1-1 (point p))
                 (:instance wb-1 (p (r-1*wb-1-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (r-1*wb-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff (point p)
                            (p (r-1*wb-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wb-1-1-witness p)))
                 )
           )
          ))

(defthmd r-1-diff-s2-iff-s2
  (iff (r-1-diff-s2 p)
       (wit-inv*s2-d-p-n-set-e-p p)))

(defun diff-s2 (p)
  (or (m0 p)
      (r-1*m1 p)
      (wa-0 p)
      (r-1*wa-1 p)
      (wa-inv-0 p)
      (r-1*wa-inv-1 p)
      (wb-0 p)
      (r-1*wb-1 p)
      (wb-inv-0 p)
      (r-1*wb-inv-1 p)))

(defthmd s2-iff-diff-s2
  (iff (s2-def-p p)
       (diff-s2 p))
  :hints (("goal"
           :use ((:instance diff-s2 (p p))
                 (:instance r-1-diff-s2 (p p))
                 (:instance iff-s2-s2-e-or-witinv*s2-d-n-e (point p))
                 (:instance s2-not-d-n-s2-not-e (point p))
                 (:instance r-1-diff-s2-iff-s2 (p p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance m0 (p p))
                 (:instance wa-0 (p p))
                 (:instance wb-0 (p p))
                 (:instance wa-inv-0 (p p))
                 (:instance wb-inv-0 (p p))
                 )
           :in-theory nil
           )))

(defun-sk rot-a*s2-not-e-1 (point)
  (exists p
          (and (s2-not-e p)
               (m-= (m-* (a-rotation (acl2-sqrt 2)) p)
                    point))))

(defun rot-a*s2-not-e (p)
  (and (point-in-r3 p)
       (rot-a*s2-not-e-1 p)))

(defun-sk rot-a*-e-1 (point)
  (exists p
          (and (set-e-p p)
               (m-= (m-* (a-rotation (acl2-sqrt 2)) p)
                    point))))

(defun rot-a*-e (p)
  (and (point-in-r3 p)
       (rot-a*-e-1 p)))

(defun rot-a*s2-e-or-e (p)
  (or (rot-a*s2-not-e p)
      (rot-a*-e p)))

(defthmd s2-iff-rot-a*s2-e-or-e-1
  (implies (point-in-r3 p)
           (m-= (m-* (a-rotation (acl2-sqrt 2))
                     (a-inv-rotation (acl2-sqrt 2))
                     p)
                p))
  :hints (("goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (a-rotation (acl2-sqrt 2)))
                            (b (a-inv-rotation (acl2-sqrt 2)))
                            (c p))
                 )
           :in-theory (e/d () (a-rotation a-inv-rotation m-* m-= id-rotation acl2-sqrt point-in-r3 array2p m-*point-id=point aref2 b-rotation b-inv-rotation (:executable-counterpart id-rotation)))
           )))

(defthmd s2-iff-rot-a*s2-e-or-e
  (iff (s2-def-p p)
       (rot-a*s2-e-or-e p))
  :hints (("goal"
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rot-a*s2-e-or-e (p p))
                 (:instance rot-a*-e (p p))
                 (:instance rot-a*s2-not-e (p p))
                 (:instance rot-a*-e-1-suff (point p)
                            (p (m-* (a-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance rot-a*s2-not-e-1-suff (point p)
                            (p (m-* (a-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance s2-iff-rot-a*s2-e-or-e-1 (p p))
                 (:instance s2-not-e (point (m-* (a-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance s2-def-p (point p))
                 (:instance rot*p-on-s2 (p p)
                            (rot (a-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance s2-def-p (point (m-* (a-inv-rotation (acl2-sqrt 2)) p)))
                 )
           )
          ("subgoal 2"
           :use ((:instance rot-a*s2-not-e (p p))
                 (:instance rot-a*s2-not-e-1 (point p))
                 (:instance s2-not-e (point (rot-a*s2-not-e-1-witness p)))
                 (:instance s2-def-p-p=>p1
                            (p (m-* (a-rotation (acl2-sqrt 2))
                                    (rot-a*s2-not-e-1-witness p)))
                            (p1 p))
                 (:instance rot*p-on-s2 (p (rot-a*s2-not-e-1-witness p))
                            (rot (a-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-a*s2-e-or-e (p p))

                 (:instance rot-a*-e (p p))
                 (:instance rot-a*-e-1 (point p))
                 (:instance set-e-p (point (rot-a*-e-1-witness p)))
                 (:instance efunc=> (point (rot-a*-e-1-witness p)))
                 (:instance r3-rotationp-r-theta
                            (angle (* (efunc-witness (rot-a*-e-1-witness p))
                                      (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
                            (n (efunc-witness (rot-a*-e-1-witness p)))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness
                                0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*p-on-s2 (p (exists-d-p-witness (efunc-witness (rot-a*-e-1-witness p))
                                                               (rot-a*-e-1-witness p)))
                            (rot (rotation-3d (* (efunc-witness (rot-a*-e-1-witness p))
                                                 (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance s2-def-p-p=>p1 (p (m-* (rotation-3d (* (efunc-witness (rot-a*-e-1-witness p))
                                                                   (exists-in-interval-but-not-in-angle-sequence-witness
                                                                    0 (* 2 (acl2-pi))))
                                                                (point-on-s2-not-d))
                                                   (exists-d-p-witness (efunc-witness (rot-a*-e-1-witness p))
                                                                       (rot-a*-e-1-witness p))))
                            (p1 (rot-a*-e-1-witness p)))
                 (:instance rot*p-on-s2 (p (rot-a*-e-1-witness p))
                            (rot (a-rotation (acl2-sqrt 2))))
                 (:instance d-p (point (exists-d-p-witness (efunc-witness (rot-a*-e-1-witness p))
                                                           (rot-a*-e-1-witness p))))
                 (:instance s2-def-p-p=>p1 (p (m-* (a-rotation (acl2-sqrt 2))
                                                   (rot-a*-e-1-witness p)))
                            (p1 p))
                 )
           )
          ))

(defthmd p1=p2-n-e-p1=>e-p2
  (implies (and (m-= p1 p2)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (set-e-p p1))
           (set-e-p p2))
  :hints (("goal"
           :use ((:instance set-e-p (point p1))
                 (:instance efunc=> (point p1))
                 (:instance set-e-p (point p2))
                 (:instance efunc-suff (point p2) (n (efunc-witness p1)))
                 (:instance exists-d-p-suff (point p2)
                            (n (efunc-witness p1))
                            (p (exists-d-p-witness (efunc-witness p1)
                                                   p1)))
                 )
           :in-theory nil
           )))

(defthmd p1=p2-n-s2-e-p1=>s2-e-p2
  (implies (and (m-= p1 p2)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (s2-not-e p1))
           (s2-not-e p2))
  :hints (("goal"
           :use ((:instance s2-not-e (point p1))
                 (:instance s2-not-e (point p2))
                 (:instance s2-def-p-p=>p1 (p p1) (p1 p2))
                 (:instance p1=p2-n-e-p1=>e-p2 (p2 p1) (p1 p2))
                 )
           :in-theory nil
           ))
  )

(defthmd a*p1=p-n-a*p2=p=>p1=p2-1
  (implies (and (m-= m1 m2)
                (m-= m3 m2))
           (m-= m1 m3)))

(defthmd a*p1=p-n-a*p2=p=>p1=p2-2
  (implies (and (m-= (m-* a b c) (m-* p q r))
                (m-= (m-* a b) d)
                (m-= (m-* p q) s)
                (m-= (m-* d c) e)
                (m-= (m-* s r) t1))
           (m-= e t1)))

(defthmd a*p1=p-n-a*p2=p=>p1=p2
  (implies (and (point-in-r3 point)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= (m-* (a-rotation (acl2-sqrt 2)) p1) point)
                (m-= (m-* (a-rotation (acl2-sqrt 2)) p2) point))
           (m-= p1 p2))
  :hints (("goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-1
                            (m (m-* (a-rotation (acl2-sqrt 2)) p1))
                            (n (m-* (a-rotation (acl2-sqrt 2)) p2))
                            (p (a-inv-rotation (acl2-sqrt 2))))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (a-inv-rotation (acl2-sqrt 2)))
                            (b (a-rotation (acl2-sqrt 2)))
                            (c p1))
                 (:instance m-*point-id=point (p1 p2))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (a-inv-rotation (acl2-sqrt 2)))
                            (b (a-rotation (acl2-sqrt 2)))
                            (c p2))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2-1 (m1 (m-* (a-rotation (acl2-sqrt 2)) p1))
                            (m2 point)
                            (m3 (m-* (a-rotation (acl2-sqrt 2)) p2)))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2-2
                            (a (a-inv-rotation (acl2-sqrt 2)))
                            (b (a-rotation (acl2-sqrt 2)))
                            (c p1)
                            (p (a-inv-rotation (acl2-sqrt 2)))
                            (q (a-rotation (acl2-sqrt 2)))
                            (r p2)
                            (d (id-rotation))
                            (s (id-rotation))
                            (e p1)
                            (t1 p2))
                 )
           :in-theory nil
           )))

(defthmd rot-a*-e=>not-rot-a*s2-not-e
  (implies (rot-a*-e p)
           (not (rot-a*s2-not-e p)))
  :hints (("goal"
           :use ((:instance rot-a*-e (p p))
                 (:instance rot-a*-e-1 (point p))
                 (:instance set-e-p (point (rot-a*-e-1-witness p)))
                 (:instance rot-a*s2-not-e (p p))
                 (:instance rot-a*s2-not-e-1 (point p))
                 (:instance s2-not-e (point (rot-a*s2-not-e-1-witness p)))
                 (:instance s2-def-p (point (rot-a*s2-not-e-1-witness p)))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2 (point p)
                            (p1 (rot-a*-e-1-witness p))
                            (p2 (rot-a*s2-not-e-1-witness p)))
                 (:instance p1=p2-n-e-p1=>e-p2 (p1 (rot-a*-e-1-witness p))
                            (p2 (rot-a*s2-not-e-1-witness p)))
                 )
           :in-theory nil
           )))

(defun-sk rot-b*s2-not-e-1 (point)
  (exists p
          (and (s2-not-e p)
               (m-= (m-* (b-rotation (acl2-sqrt 2)) p)
                    point))))

(defun rot-b*s2-not-e (p)
  (and (point-in-r3 p)
       (rot-b*s2-not-e-1 p)))

(defun-sk rot-b*-e-1 (point)
  (exists p
          (and (set-e-p p)
               (m-= (m-* (b-rotation (acl2-sqrt 2)) p)
                    point))))

(defun rot-b*-e (p)
  (and (point-in-r3 p)
       (rot-b*-e-1 p)))

(defun rot-b*s2-e-or-e (p)
  (or (rot-b*s2-not-e p)
      (rot-b*-e p)))

(defthmd s2-iff-rot-b*s2-e-or-e-1-1
  (implies (and (m-= (m-* b b-inv) id)
                (m-= (m-* id p) p1))
           (m-= (m-* b b-inv p) p1)))

(defthmd s2-iff-rot-b*s2-e-or-e-1
  (implies (point-in-r3 p)
           (m-= (m-* (b-rotation (acl2-sqrt 2))
                     (b-inv-rotation (acl2-sqrt 2))
                     p)
                p))
  :hints (("goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (b-rotation (acl2-sqrt 2)))
                            (b (b-inv-rotation (acl2-sqrt 2)))
                            (c p))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (b-rotation (acl2-sqrt 2)))
                            (b (b-inv-rotation (acl2-sqrt 2)))
                            (c p))
                 (:instance s2-iff-rot-b*s2-e-or-e-1-1
                            (b (b-rotation (acl2-sqrt 2)))
                            (b-inv (b-inv-rotation (acl2-sqrt 2)))
                            (id (id-rotation))
                            (p p)
                            (p1 p))
                 )
           :in-theory nil
           )))

(defthmd s2-iff-rot-b*s2-e-or-e
  (iff (s2-def-p p)
       (rot-b*s2-e-or-e p))
  :hints (("goal"
           :in-theory nil
           )
          ("subgoal 1"
           :use ((:instance rot-b*s2-e-or-e (p p))
                 (:instance rot-b*-e (p p))
                 (:instance rot-b*s2-not-e (p p))
                 (:instance rot-b*-e-1-suff (point p)
                            (p (m-* (b-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance rot-b*s2-not-e-1-suff (point p)
                            (p (m-* (b-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance s2-iff-rot-b*s2-e-or-e-1 (p p))
                 (:instance s2-not-e (point (m-* (b-inv-rotation (acl2-sqrt 2)) p)))
                 (:instance s2-def-p (point p))
                 (:instance rot*p-on-s2 (p p)
                            (rot (b-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance s2-def-p (point (m-* (b-inv-rotation (acl2-sqrt 2)) p)))
                 )
           )
          ("subgoal 2"
           :use ((:instance rot-b*s2-not-e (p p))
                 (:instance rot-b*s2-not-e-1 (point p))
                 (:instance s2-not-e (point (rot-b*s2-not-e-1-witness p)))
                 (:instance s2-def-p-p=>p1
                            (p (m-* (b-rotation (acl2-sqrt 2))
                                    (rot-b*s2-not-e-1-witness p)))
                            (p1 p))
                 (:instance rot*p-on-s2 (p (rot-b*s2-not-e-1-witness p))
                            (rot (b-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot-b*s2-e-or-e (p p))

                 (:instance rot-b*-e (p p))
                 (:instance rot-b*-e-1 (point p))
                 (:instance set-e-p (point (rot-b*-e-1-witness p)))
                 (:instance efunc=> (point (rot-b*-e-1-witness p)))
                 (:instance r3-rotationp-r-theta
                            (angle (* (efunc-witness (rot-b*-e-1-witness p))
                                      (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-2-2
                            (n (efunc-witness (rot-b*-e-1-witness p)))
                            (x (exists-in-interval-but-not-in-angle-sequence-witness
                                0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance rot*p-on-s2 (p (exists-d-p-witness (efunc-witness (rot-b*-e-1-witness p))
                                                               (rot-b*-e-1-witness p)))
                            (rot (rotation-3d (* (efunc-witness (rot-b*-e-1-witness p))
                                                 (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance s2-def-p-p=>p1 (p (m-* (rotation-3d (* (efunc-witness (rot-b*-e-1-witness p))
                                                                   (exists-in-interval-but-not-in-angle-sequence-witness
                                                                    0 (* 2 (acl2-pi))))
                                                                (point-on-s2-not-d))
                                                   (exists-d-p-witness (efunc-witness (rot-b*-e-1-witness p))
                                                                       (rot-b*-e-1-witness p))))
                            (p1 (rot-b*-e-1-witness p)))
                 (:instance rot*p-on-s2 (p (rot-b*-e-1-witness p))
                            (rot (b-rotation (acl2-sqrt 2))))
                 (:instance d-p (point (exists-d-p-witness (efunc-witness (rot-b*-e-1-witness p))
                                                           (rot-b*-e-1-witness p))))
                 (:instance s2-def-p-p=>p1 (p (m-* (b-rotation (acl2-sqrt 2))
                                                   (rot-b*-e-1-witness p)))
                            (p1 p))
                 )
           )
          ))

(defthmd b*p1=p-n-b*p2=p=>p1=p2
  (implies (and (point-in-r3 point)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= (m-* (b-rotation (acl2-sqrt 2)) p1) point)
                (m-= (m-* (b-rotation (acl2-sqrt 2)) p2) point))
           (m-= p1 p2))
  :hints (("goal"
           :use ((:instance rot-angle-witness*p1!=p2-intmn-1
                            (m (m-* (b-rotation (acl2-sqrt 2)) p1))
                            (n (m-* (b-rotation (acl2-sqrt 2)) p2))
                            (p (b-inv-rotation (acl2-sqrt 2))))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (b-inv-rotation (acl2-sqrt 2)))
                            (b (b-rotation (acl2-sqrt 2)))
                            (c p1))
                 (:instance m-*point-id=point (p1 p2))
                 (:instance efunc-not-d=>rot-witness*e-func-3-1
                            (a (b-inv-rotation (acl2-sqrt 2)))
                            (b (b-rotation (acl2-sqrt 2)))
                            (c p2))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2-1 (m1 (m-* (b-rotation (acl2-sqrt 2)) p1))
                            (m2 point)
                            (m3 (m-* (b-rotation (acl2-sqrt 2)) p2)))
                 (:instance a*p1=p-n-a*p2=p=>p1=p2-2
                            (a (b-inv-rotation (acl2-sqrt 2)))
                            (b (b-rotation (acl2-sqrt 2)))
                            (c p1)
                            (p (b-inv-rotation (acl2-sqrt 2)))
                            (q (b-rotation (acl2-sqrt 2)))
                            (r p2)
                            (d (id-rotation))
                            (s (id-rotation))
                            (e p1)
                            (t1 p2))
                 )
           :in-theory nil
           )))

(defthmd rot-b*-e=>not-rot-b*s2-not-e
  (implies (rot-b*-e p)
           (not (rot-b*s2-not-e p)))
  :hints (("goal"
           :use ((:instance rot-b*-e (p p))
                 (:instance rot-b*-e-1 (point p))
                 (:instance set-e-p (point (rot-b*-e-1-witness p)))
                 (:instance rot-b*s2-not-e (p p))
                 (:instance rot-b*s2-not-e-1 (point p))
                 (:instance s2-not-e (point (rot-b*s2-not-e-1-witness p)))
                 (:instance s2-def-p (point (rot-b*s2-not-e-1-witness p)))
                 (:instance b*p1=p-n-b*p2=p=>p1=p2 (point p)
                            (p1 (rot-b*-e-1-witness p))
                            (p2 (rot-b*s2-not-e-1-witness p)))
                 (:instance p1=p2-n-e-p1=>e-p2 (p1 (rot-b*-e-1-witness p))
                            (p2 (rot-b*s2-not-e-1-witness p)))
                 )
           :in-theory nil
           )))

(defun wa-00 (p)
  (and (wa-0 p)
       (rot-a*s2-not-e p)))

(defun wa-01 (p)
  (and (wa-0 p)
       (rot-a*-e p)))

(defun wa-10 (p)
  (and (wa-1 p)
       (rot-a*s2-not-e p)))

(defun wa-11 (p)
  (and (wa-1 p)
       (rot-a*-e p)))

(defun wb-00 (p)
  (and (wb-0 p)
       (rot-b*s2-not-e p)))

(defun wb-01 (p)
  (and (wb-0 p)
       (rot-b*-e p)))

(defun wb-10 (p)
  (and (wb-1 p)
       (rot-b*s2-not-e p)))

(defun wb-11 (p)
  (and (wb-1 p)
       (rot-b*-e p)))

(defthmd wa-0-iff-wa00-or-wa01
  (iff (wa-0 p)
       (or (wa-00 p)
           (wa-01 p)))
  :hints (("goal"
           :use ((:instance wa-00 (p p))
                 (:instance wa-01 (p p))
                 (:instance s2-iff-rot-a*s2-e-or-e (p p))
                 (:instance wa-0 (p p))
                 (:instance s2-not-e (point p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance s2-d-p (point p))
                 (:instance rot-a*s2-e-or-e (p p))
                 )
           :in-theory nil
           )))

(defthmd wa-1-iff-wa10-or-wa11
  (iff (wa-1 p)
       (or (wa-10 p)
           (wa-11 p)))
  :hints (("goal"
           :use ((:instance wa-10 (p p))
                 (:instance wa-11 (p p))
                 (:instance s2-iff-rot-a*s2-e-or-e (p p))
                 (:instance wa-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance s2-d-p (point p))
                 (:instance rot-a*s2-e-or-e (p p))
                 (:instance set-e-p=>s2-def-p (point p))
                 )
           :in-theory nil
           )))

(defthmd wb-0-iff-wb00-or-wb01
  (iff (wb-0 p)
       (or (wb-00 p)
           (wb-01 p)))
  :hints (("goal"
           :use ((:instance wb-00 (p p))
                 (:instance wb-01 (p p))
                 (:instance s2-iff-rot-b*s2-e-or-e (p p))
                 (:instance wb-0 (p p))
                 (:instance s2-not-e (point p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance s2-d-p (point p))
                 (:instance rot-b*s2-e-or-e (p p))
                 )
           :in-theory nil
           )))

(defthmd wb-1-iff-wb10-or-wb11
  (iff (wb-1 p)
       (or (wb-10 p)
           (wb-11 p)))
  :hints (("goal"
           :use ((:instance wb-10 (p p))
                 (:instance wb-11 (p p))
                 (:instance s2-iff-rot-b*s2-e-or-e (p p))
                 (:instance wb-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p p))
                 (:instance s2-d-p (point p))
                 (:instance rot-b*s2-e-or-e (p p))
                 (:instance set-e-p=>s2-def-p (point p))
                 )
           :in-theory nil
           )))

(defun set-a1 (p)
  (m0 p))

(defun set-a2 (p)
  (r-1*m1 p))

(defun set-a3 (p)
  (wa-00 p))

(defun-sk set-a4-1 (point)
  (exists p
          (and (wa-10 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun set-a4 (p)
  (and (point-in-r3 p)
       (set-a4-1 p)))

(defun set-a5 (p)
  (wa-01 p))

(defun-sk set-a6-1 (point)
  (exists p
          (and (wa-11 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun set-a6 (p)
  (and (point-in-r3 p)
       (set-a6-1 p)))

(defun set-a7 (p)
  (wa-inv-0 p))

(defun set-a8 (p)
  (r-1*wa-inv-1 p))

(defun set-a9 (p)
  (wb-00 p))

(defun-sk set-a10-1 (point)
  (exists p
          (and (wb-10 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun set-a10 (p)
  (and (point-in-r3 p)
       (set-a10-1 p)))

(defun set-a11 (p)
  (wb-01 p))

(defun-sk set-a12-1 (point)
  (exists p
          (and (wb-11 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) p) point))))

(defun set-a12 (p)
  (and (point-in-r3 p)
       (set-a12-1 p)))

(defun set-a13 (p)
  (wb-inv-0 p))

(defun set-a14 (p)
  (r-1*wb-inv-1 p))

(defun r-1-setas (p)
  (or (set-a2 p)
      (set-a4 p)
      (set-a6 p)
      (set-a8 p)
      (set-a10 p)
      (set-a12 p)
      (set-a14 p)))

(defthmd r-1-setas-iff-r-1-diff-s2-1
  (implies (r-1-setas p)
           (r-1-diff-s2 p))
  :hints (("goal"
           :cases ((set-a2 p)
                   (set-a4 p)
                   (set-a6 p)
                   (set-a8 p)
                   (set-a10 p)
                   (set-a12 p)
                   (set-a14 p))
           :use ((:instance r-1-setas (p p))
                 (:instance r-1-diff-s2 (p p)))
           :in-theory nil
           )
          ("subgoal 7"
           :use ((:instance set-a2 (p p))
                 )
           )
          ("subgoal 6"
           :use ((:instance set-a4 (p p))
                 (:instance set-a4-1 (point p))
                 (:instance r-1*wa-1 (p p))
                 (:instance r-1*wa-1-1-suff (point p) (p (set-a4-1-witness p)))
                 (:instance wa-1-iff-wa10-or-wa11 (p (set-a4-1-witness p)))
                 )
           )
          ("subgoal 5"
           :use ((:instance set-a6 (p p))
                 (:instance set-a6-1 (point p))
                 (:instance r-1*wa-1 (p p))
                 (:instance r-1*wa-1-1-suff (point p) (p (set-a6-1-witness p)))
                 (:instance wa-1-iff-wa10-or-wa11 (p (set-a6-1-witness p)))
                 )
           )
          ("subgoal 4"
           :use ((:instance set-a8 (p p))
                 )
           )
          ("subgoal 3"
           :use ((:instance set-a10 (p p))
                 (:instance set-a10-1 (point p))
                 (:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-1-1-suff (point p) (p (set-a10-1-witness p)))
                 (:instance wb-1-iff-wb10-or-wb11 (p (set-a10-1-witness p)))
                 )
           )
          ("subgoal 2"
           :use ((:instance set-a12 (p p))
                 (:instance set-a12-1 (point p))
                 (:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-1-1-suff (point p) (p (set-a12-1-witness p)))
                 (:instance wb-1-iff-wb10-or-wb11 (p (set-a12-1-witness p)))
                 )
           )
          ("subgoal 1"
           :use (:instance set-a14 (p p))
           )
          ))

(defthmd r-1-setas-iff-r-1-diff-s2-2
  (implies (r-1-diff-s2 p)
           (r-1-setas p))
  :hints (("goal"
           :use ((:instance r-1-diff-s2 (p p))
                 (:instance r-1-setas (p p)))
           :cases ((r-1*m1 p)
                   (r-1*wa-1 p)
                   (r-1*wa-inv-1 p)
                   (r-1*wb-1 p)
                   (r-1*wb-inv-1 p))
           :in-theory nil
           )
          ("subgoal 5"
           :use (:instance set-a2 (p p))
           )
          ("subgoal 4"
           :use ((:instance r-1*wa-1 (p p))
                 (:instance r-1*wa-1-1 (point p))
                 (:instance wa-1-iff-wa10-or-wa11 (p (r-1*wa-1-1-witness p)))
                 (:instance set-a4 (p p))
                 (:instance set-a4-1-suff (point p) (p (r-1*wa-1-1-witness p)))
                 (:instance set-a6 (p p))
                 (:instance set-a6-1-suff (point p) (p (r-1*wa-1-1-witness p)))
                 )
           )
          ("subgoal 3"
           :use (:instance set-a8 (p p))
           )
          ("subgoal 2"
           :use ((:instance r-1*wb-1 (p p))
                 (:instance r-1*wb-1-1 (point p))
                 (:instance wb-1-iff-wb10-or-wb11 (p (r-1*wb-1-1-witness p)))
                 (:instance set-a10 (p p))
                 (:instance set-a10-1-suff (point p) (p (r-1*wb-1-1-witness p)))
                 (:instance set-a12 (p p))
                 (:instance set-a12-1-suff (point p) (p (r-1*wb-1-1-witness p)))
                 )
           )
          ("subgoal 1"
           :use (:instance set-a14 (p p))
           )
          ))

(defthmd r-1-setas-iff-r-1-diff
  (iff (r-1-diff-s2 p)
       (r-1-setas p)))

(defun-sk set-a-inv-a3-1 (point)
  (exists p
          (and (set-a3 p)
               (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) p)
                    point))))

(defun set-a-inv-a3 (p)
  (and (point-in-r3 p)
       (set-a-inv-a3-1 p)))

(defun-sk set-a-inv-r-a4-1 (point)
  (exists p
          (and (set-a4 p)
               (m-= (m-* (a-inv-rotation (acl2-sqrt 2))
                         (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                         p)
                    point))))

(defun set-a-inv-r-a4 (p)
  (and (point-in-r3 p)
       (set-a-inv-r-a4-1 p)))

(defun-sk set-r-1-a-inv-a5-1 (point)
  (exists p
          (and (set-a5 p)
               (m-= (m-*
                     (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                     (a-inv-rotation (acl2-sqrt 2))
                     p)
                    point))))

(defun set-r-1-a-inv-a5 (p)
  (and (point-in-r3 p)
       (set-r-1-a-inv-a5-1 p)))

(defun-sk set-r-1-a-inv-r-a6-1 (point)
  (exists p
          (and (set-a6 p)
               (m-= (m-*
                     (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                     (a-inv-rotation (acl2-sqrt 2))
                     (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                     p)
                    point))))

(defun set-r-1-a-inv-r-a6 (p)
  (and (point-in-r3 p)
       (set-r-1-a-inv-r-a6-1 p)))

(defthmd a-inv-diff-a-s2-d=>rot-a*s2-not-e-1
  (m-= (rotation (list (wa-inv)) (acl2-sqrt 2))
       (a-inv-rotation (acl2-sqrt 2)))
  :hints (("goal"
           :use ((:instance wa-inv)
                 (:instance wa)
                 (:instance rotation (w '(#\b)) (x (acl2-sqrt 2)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m*id=m (m1 (a-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (a-inv-rotation (acl2-sqrt 2))))
                 )
           :in-theory nil
           ))
  )

(defthmd a-inv-diff-a-s2-d=>rot-a*s2-not-e-2
  (implies (and (m-= rot-lwa-inv a-inv)
                (m-= (m-* rot-lwa-inv wit) p)
                (m-= (m-* a a-inv) id)
                (m-= (m-* id wit) wit1))
           (m-= (m-* a p) wit1)))

(defthmd a-inv-diff-a-s2-d=>rot-a*s2-not-e
  (implies (and (a-inv-diff-a-s2-d-p p)
                (s2-not-e p))
           (rot-a*s2-not-e (a-inv-diff-a-s2-d-p-1-witness p)))
  :hints (("goal"
           :use ((:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance rot-a*s2-not-e (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance rot-a*s2-not-e-1-suff (point (a-inv-diff-a-s2-d-p-1-witness p))
                            (p p))
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-2
                            (rot-lwa-inv (rotation (list (wa-inv)) (acl2-sqrt 2)))
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (wit (a-inv-diff-a-s2-d-p-1-witness p))
                            (wit1 (a-inv-diff-a-s2-d-p-1-witness p))
                            (id (id-rotation))
                            (a (a-rotation (acl2-sqrt 2)))
                            (p p))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (a-inv-diff-a-s2-d-p-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd a-inv-diff-a-s2-d=>wa-00-orwa-10-wit
  (implies (and (a-inv-diff-a-s2-d-p p)
                (s2-not-e p))
           (or (wa-00 (a-inv-diff-a-s2-d-p-1-witness p))
               (wa-10 (a-inv-diff-a-s2-d-p-1-witness p))))
  :hints (("goal"
           :use ((:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-00 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-10 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-0 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-not-e (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance rot-a*s2-not-e (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance rot-a*s2-not-e-1 (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e (p p))
                 )
           :in-theory nil
           ))
  )

(defthmd a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-1
  (implies (and (m-= rotl-a-inv a-inv)
                (m-= (m-* rotl-a-inv wit) p))
           (m-= (m-* a-inv wit) p)))

(defthmd a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-2
  (implies (and (m-= wit-0 id)
                (m-= (m-* r r-1) wit-0)
                (m-= (m-* a-inv-1 id ) a-inv)
                (m-= (m-* a-inv wit) p))
           (m-= (m-* a-inv-1 r r-1 wit) p)))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-3
   (m-= (m-* (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
			   0 (* 2 (acl2-pi)))
			  (point-on-s2-not-d))
	     (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
			      0 (* 2 (acl2-pi))))
			  (point-on-s2-not-d)))
	(rotation-3d 0 (point-on-s2-not-d)))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2
			     (angle1 (exists-in-interval-but-not-in-angle-sequence-witness
				      0 (* 2 (acl2-pi))))
			     (angle2 (- (exists-in-interval-but-not-in-angle-sequence-witness
					 0 (* 2 (acl2-pi)))))
			     (u (point-on-s2-not-d)))
		  (:instance exists-point-on-s2-not-d-2)
		  (:instance s2-def-p (point (point-on-s2-not-d)))
		  (:instance witness-not-in-angle-sequence)
		  )
	    :in-theory (e/d (m-=) (point-on-s2-not-d rotation-3d s2-def-p point-in-r3 aref2 m-* rotation))
	    )))
 )

(defthmd a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-4
  (realp (- (exists-in-interval-but-not-in-angle-sequence-witness
             0 (* 2 (acl2-pi)))))
  :hints (("goal"
           :use (:instance witness-not-in-angle-sequence)
           )))

(defthmd a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4
  (implies (and (a-inv-diff-a-s2-d-p p)
                (s2-not-e p))
           (or (set-a-inv-a3 p)
               (set-a-inv-r-a4 p)))
  :hints (("goal"
           :use ((:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1 (p p))
                 (:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1 (p p))
                 (:instance wa-00 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-10 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-0 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-not-e (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p-equivalence-2 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance a-inv-diff-a-s2-d=>wa-00-orwa-10-wit (p p))
                 (:instance set-a-inv-a3 (p p))
                 (:instance set-a-inv-a3-1-suff (point p) (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance set-a3 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-1
                            (rotl-a-inv (rotation (list (wa-inv)) (acl2-sqrt 2)))
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (wit (a-inv-diff-a-s2-d-p-1-witness p))
                            (p p))
                 (:instance set-a4
                            (p (m-*
                                (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                (a-inv-diff-a-s2-d-p-1-witness p))))
                 (:instance set-a4-1-suff
                            (point (m-*
                                    (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (a-inv-diff-a-s2-d-p-1-witness p)))
                            (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance set-a-inv-r-a4 (p p))
                 (:instance set-a-inv-r-a4-1-suff (point p)
                            (p (m-*
                                (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                (a-inv-diff-a-s2-d-p-1-witness p))))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-2
                            (p p)
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (a-inv-1 (a-inv-rotation (acl2-sqrt 2)))
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (id (id-rotation))
                            (wit-0 (rotation-3d 0 (point-on-s2-not-d)))
                            (wit (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-3)
                 (:instance r-theta-0=id
                            (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (a-inv-diff-a-s2-d-p-1-witness p))
                            (rot (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp
                            (m (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                0 (* 2 (acl2-pi))))
                                            (point-on-s2-not-d))))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-4)
                 )
           :in-theory nil
           )
          ))

(defun-sk a-inv*wa-00-or-wa-10-1 (point)
  (exists p
          (and (or (wa-00 p)
                   (wa-10 p))
               (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) p)
                    point))))

(defun a-inv*wa-00-or-wa-10 (p)
  (and (point-in-r3 p)
       (a-inv*wa-00-or-wa-10-1 p)))

(defthmd a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d-1
  (implies (and (m-= (m-* a-inv r-wit wit) p)
                (m-= (m-* r-1-wit wit-wit) wit)
                (m-= (m-* r-wit r-1-wit) id)
                (m-= (m-* a-inv id) a-inv-1)
                )
           (m-= (m-* a-inv-1 wit-wit) p)))


(defthmd a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d-2
  (implies (or (set-a-inv-a3 p)
               (set-a-inv-r-a4 p))
           (a-inv*wa-00-or-wa-10 p))
  :hints (("goal"
           :cases ((set-a-inv-a3 p)
                   (set-a-inv-r-a4 p))
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance set-a-inv-a3 (p p))
                 (:instance set-a-inv-a3-1 (point p))
                 (:instance set-a3 (p (set-a-inv-a3-1-witness p)))
                 (:instance a-inv*wa-00-or-wa-10-1-suff (point p)
                            (p (set-a-inv-a3-1-witness p)))
                 (:instance a-inv*wa-00-or-wa-10 (p p))
                 )
           )
          ("subgoal 1"
           :use ((:instance set-a-inv-r-a4 (p p))
                 (:instance set-a-inv-r-a4-1 (point p))
                 (:instance set-a4 (p (set-a-inv-r-a4-1-witness p)))
                 (:instance set-a4-1 (point (set-a-inv-r-a4-1-witness p)))
                 (:instance a-inv*wa-00-or-wa-10-1-suff (point p)
                            (p (set-a4-1-witness (set-a-inv-r-a4-1-witness p))))
                 (:instance a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d-1
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (a-inv-1 (a-inv-rotation (acl2-sqrt 2)))
                            (r-wit (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi)))
                                                (point-on-s2-not-d)))
                            (wit (set-a-inv-r-a4-1-witness p))
                            (p p)
                            (r-1-wit (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                      0 (* 2 (acl2-pi))))
                                                  (point-on-s2-not-d)))
                            (wit-wit (set-a4-1-witness (set-a-inv-r-a4-1-witness p)))
                            (id (id-rotation))
                            )
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-3)
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance r-theta-0=id (u (point-on-s2-not-d)))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance a-inv*wa-00-or-wa-10 (p p))
                 )
           )
          ))

(defthmd a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d-3
  (implies (and (m-= (m-* a-rot wit-wit) wit)
                (m-= (m-* a-inv wit) p)
                (m-= (m-* a-inv a-rot) id)
                (m-= (m-* id wit-wit) wit-wit1))
           (m-= wit-wit1 p)))

(defthmd a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d
  (implies (or (set-a-inv-a3 p)
               (set-a-inv-r-a4 p))
           (and (a-inv-diff-a-s2-d-p p)
                (s2-not-e p)))
  :hints (("goal"
           :use ((:instance a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d-2 (p p))
                 (:instance a-inv*wa-00-or-wa-10 (p p))
                 (:instance a-inv*wa-00-or-wa-10-1 (point p))
                 (:instance wa-00 (p (a-inv*wa-00-or-wa-10-1-witness p)))
                 (:instance wa-10 (p (a-inv*wa-00-or-wa-10-1-witness p)))
                 (:instance wa-0 (p (a-inv*wa-00-or-wa-10-1-witness p)))
                 (:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1-suff (p p)
                            (p1 (a-inv*wa-00-or-wa-10-1-witness p)))
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-1
                            (rotl-a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (a-inv (rotation (list (wa-inv)) (acl2-sqrt 2)))
                            (wit (a-inv*wa-00-or-wa-10-1-witness p))
                            (p p))
                 (:instance rot-a*s2-not-e (p (a-inv*wa-00-or-wa-10-1-witness p)))
                 (:instance rot-a*s2-not-e-1 (point (a-inv*wa-00-or-wa-10-1-witness p)))
                 (:instance a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d-3
                            (a-rot (a-rotation (acl2-sqrt 2)))
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (wit-wit (rot-a*s2-not-e-1-witness (a-inv*wa-00-or-wa-10-1-witness p)))
                            (wit-wit1 (rot-a*s2-not-e-1-witness (a-inv*wa-00-or-wa-10-1-witness p)))
                            (wit (a-inv*wa-00-or-wa-10-1-witness p))
                            (p p)
                            (id (id-rotation)))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance s2-not-e (point (rot-a*s2-not-e-1-witness (a-inv*wa-00-or-wa-10-1-witness p))))
                 (:instance s2-def-p (point (rot-a*s2-not-e-1-witness (a-inv*wa-00-or-wa-10-1-witness p))))
                 (:instance m-*point-id=point (p1 (rot-a*s2-not-e-1-witness (a-inv*wa-00-or-wa-10-1-witness p))))
                 (:instance p1=p2-n-s2-e-p1=>s2-e-p2 (p1 (rot-a*s2-not-e-1-witness (a-inv*wa-00-or-wa-10-1-witness p)))
                            (p2 p))
                 (:instance wa-1 (p (a-inv*wa-00-or-wa-10-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd a-1-a3ora-1-r-a4-iff-a-inv-diff-a-s2-d
  (iff (or (set-a-inv-a3 p)
           (set-a-inv-r-a4 p))
       (and (a-inv-diff-a-s2-d-p p)
            (s2-not-e p)))
  :hints (("goal"
           :use ((:instance a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4))
           )))

(defthmd a-inv-diff-a-s2-d=>rot-a*-e
  (implies (and (a-inv-diff-a-s2-d-p p)
                (set-e-p p))
           (rot-a*-e (a-inv-diff-a-s2-d-p-1-witness p)))
  :hints (("goal"
           :use ((:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance rot-a*-e (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance rot-a*-e-1-suff (point (a-inv-diff-a-s2-d-p-1-witness p))
                            (p p))
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-2
                            (rot-lwa-inv (rotation (list (wa-inv)) (acl2-sqrt 2)))
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (wit (a-inv-diff-a-s2-d-p-1-witness p))
                            (wit1 (a-inv-diff-a-s2-d-p-1-witness p))
                            (id (id-rotation))
                            (a (a-rotation (acl2-sqrt 2)))
                            (p p))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (a-inv-diff-a-s2-d-p-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd a-inv-diff-a-s2-d=>wa-01-orwa-11-wit
  (implies (and (a-inv-diff-a-s2-d-p p)
                (set-e-p p))
           (or (wa-01 (a-inv-diff-a-s2-d-p-1-witness p))
               (wa-11 (a-inv-diff-a-s2-d-p-1-witness p))))
  :hints (("goal"
           :use ((:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-01 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-11 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-0 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-not-e (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance rot-a*-e (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance rot-a*-e-1 (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance a-inv-diff-a-s2-d=>rot-a*-e (p p))
                 )
           :in-theory nil
           ))
  )

(defun-sk a-inv*wa-01-or-wa-11-1 (point)
  (exists p
          (and (or (wa-01 p)
                   (wa-11 p))
               (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) p)
                    point))))

(defun a-inv*wa-01-or-wa-11 (p)
  (and (point-in-r3 p)
       (a-inv*wa-01-or-wa-11-1 p)))

(defthmd a-inv-diff-a-s2-d=>a-inv*wa-01-or-wa-11
  (implies (and (a-inv-diff-a-s2-d-p p)
                (set-e-p p))
           (a-inv*wa-01-or-wa-11 p))
  :hints (("goal"
           :use ((:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1 (p p))
                 (:instance wa-01 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-11 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-0 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance wa-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-not-e (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p-equivalence-2 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance a-inv-diff-a-s2-d=>wa-01-orwa-11-wit (p p))
                 (:instance a-inv*wa-01-or-wa-11 (p p))
                 (:instance a-inv*wa-01-or-wa-11-1-suff (point p) (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-1
                            (rotl-a-inv (rotation (list (wa-inv)) (acl2-sqrt 2)))
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (wit (a-inv-diff-a-s2-d-p-1-witness p))
                            (p p))
                 )
           :in-theory nil
           )
          ))

(defthmd a-inv*wa-01-or-wa-11=>a-inv-diff-a-s2-d-1
  (implies (and (m-= (m-* a-inv wa) p)
                (m-= rot-a-inv a-inv))
           (m-= (m-* rot-a-inv wa) p)))

(defthmd a-inv*wa-01-or-wa-11=>a-inv-diff-a-s2-d-2
  (implies (and (m-= (m-* a-inv wa-0111) p)
                (m-= (m-* a rot-wit) wa-0111)
                (m-= (m-* a-inv a) id)
                (m-= (m-* id rot-wit) rot-wit1))
           (m-= rot-wit1 p)))


(defthmd a-inv*wa-01-or-wa-11=>a-inv-diff-a-s2-d
  (implies (a-inv*wa-01-or-wa-11 p)
           (and (a-inv-diff-a-s2-d-p p)
                (set-e-p p)))
  :hints (("goal"
           :use ((:instance a-inv*wa-01-or-wa-11 (p p))
                 (:instance a-inv*wa-01-or-wa-11-1 (point p))
                 (:instance wa-01 (p (a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance wa-0 (p (a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance wa-11 (p (a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance wa-1 (p (a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance rot-a*-e (p (a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance rot-a*-e-1 (point (a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1-suff (p1 (a-inv*wa-01-or-wa-11-1-witness p)) (p p))
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-1)
                 (:instance a-inv*wa-01-or-wa-11=>a-inv-diff-a-s2-d-1
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (wa (a-inv*wa-01-or-wa-11-1-witness p))
                            (p p)
                            (rot-a-inv (rotation (list (wa-inv)) (acl2-sqrt 2))))
                 (:instance a-inv*wa-01-or-wa-11=>a-inv-diff-a-s2-d-2
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (wa-0111 (a-inv*wa-01-or-wa-11-1-witness p))
                            (p p)
                            (a (a-rotation (acl2-sqrt 2)))
                            (rot-wit (rot-a*-e-1-witness (a-inv*wa-01-or-wa-11-1-witness p)))
                            (id (id-rotation))
                            (rot-wit1 (rot-a*-e-1-witness (a-inv*wa-01-or-wa-11-1-witness p)))
                            )
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance set-e-p=>s2-def-p (point (rot-a*-e-1-witness (a-inv*wa-01-or-wa-11-1-witness p))))
                 (:instance s2-def-p (point (rot-a*-e-1-witness (a-inv*wa-01-or-wa-11-1-witness p))))
                 (:instance m-*point-id=point (p1 (rot-a*-e-1-witness (a-inv*wa-01-or-wa-11-1-witness p))))
                 (:instance p1=p2-n-e-p1=>e-p2 (p1 (rot-a*-e-1-witness (a-inv*wa-01-or-wa-11-1-witness p)))
                            (p2 p))
                 )
           :in-theory nil
           )))

(defthmd a-inv*wa-01-or-wa-11-iff-a-inv-diff-a-s2-d
  (iff (a-inv*wa-01-or-wa-11 p)
       (and (a-inv-diff-a-s2-d-p p)
            (set-e-p p)))
  :hints (("goal"
           :use ((:instance a-inv*wa-01-or-wa-11=>a-inv-diff-a-s2-d)
                 (:instance a-inv-diff-a-s2-d=>a-inv*wa-01-or-wa-11))
           )))

(defun-sk r-1*a-inv*wa-01-or-wa-11-1 (point)
  (exists p
          (and (a-inv*wa-01-or-wa-11 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                          0 (* 2 (acl2-pi))))
                                      (point-on-s2-not-d))
                         p)
                    point))))

(defun r-1*a-inv*wa-01-or-wa-11 (p)
  (and (point-in-r3 p)
       (r-1*a-inv*wa-01-or-wa-11-1 p)))

(defthmd r-1-a-1-a5orr-1-a-1-r-a6-iff-a-inv-diff-a-s2-d-1
  (implies (and (m-= (m-* r-1 w11) wit)
                (m-= (m-* r-1 a-inv r wit) p)
                (m-= (m-* r r-1) r0)
                (m-= r0 id)
                (m-= (m-* a-inv id) a-inv1))
           (m-= (m-* r-1 a-inv1 w11) p)))

(defthmd r-1-a-1-a5orr-1-a-1-r-a6-=>-a-inv-diff-a-s2-d
  (implies (or (set-r-1-a-inv-a5 p)
               (set-r-1-a-inv-r-a6 p))
           (r-1*a-inv*wa-01-or-wa-11 p))
  :hints (("goal"
           :use ((:instance set-r-1-a-inv-a5 (p p))
                 (:instance set-r-1-a-inv-a5-1 (point p))
                 (:instance set-a5 (p (set-r-1-a-inv-a5-1-witness p)))
                 (:instance r-1*a-inv*wa-01-or-wa-11 (p p))
                 (:instance r-1*a-inv*wa-01-or-wa-11-1-suff
                            (p (m-* (a-inv-rotation (acl2-sqrt 2))
                                    (set-r-1-a-inv-a5-1-witness p)))
                            (point p))
                 (:instance a-inv*wa-01-or-wa-11
                            (p (m-* (a-inv-rotation (acl2-sqrt 2))
                                    (set-r-1-a-inv-a5-1-witness p))))
                 (:instance a-inv*wa-01-or-wa-11-1-suff
                            (point (m-* (a-inv-rotation (acl2-sqrt 2))
                                        (set-r-1-a-inv-a5-1-witness p)))
                            (p (set-r-1-a-inv-a5-1-witness p)))
                 (:instance wa-01 (p (set-r-1-a-inv-a5-1-witness p)))
                 (:instance wa-0 (p (set-r-1-a-inv-a5-1-witness p)))
                 (:instance s2-not-e (point (set-r-1-a-inv-a5-1-witness p)))
                 (:instance s2-def-p (point (set-r-1-a-inv-a5-1-witness p)))
                 (:instance set-r-1-a-inv-r-a6 (p p))
                 (:instance set-r-1-a-inv-r-a6-1 (point p))
                 (:instance set-a6 (p (set-r-1-a-inv-r-a6-1-witness p)))
                 (:instance set-a6-1 (point (set-r-1-a-inv-r-a6-1-witness p)))
                 (:instance r-1*a-inv*wa-01-or-wa-11 (p p))
                 (:instance r-1*a-inv*wa-01-or-wa-11-1-suff
                            (p (m-* (a-inv-rotation (acl2-sqrt 2))
                                    (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                            (point p))
                 (:instance a-inv*wa-01-or-wa-11
                            (p (m-* (a-inv-rotation (acl2-sqrt 2))
                                    (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p)))))
                 (:instance a-inv*wa-01-or-wa-11-1-suff
                            (point (m-* (a-inv-rotation (acl2-sqrt 2))
                                        (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                            (p (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance r-1-a-1-a5orr-1-a-1-r-a6-iff-a-inv-diff-a-s2-d-1
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (w11 (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p)))
                            (wit (set-r-1-a-inv-r-a6-1-witness p))
                            (p p)
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (r0 (rotation-3d 0 (point-on-s2-not-d)))
                            (id (id-rotation))
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (a-inv1 (a-inv-rotation (acl2-sqrt 2))))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance r-theta-0=id (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance wa-01 (p (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance wa-11 (p (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance wa-0 (p (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance wa-1 (p (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance s2-d-p-equivalence-1 (p (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance s2-d-p (point (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance s2-def-p (point (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (set-a6-1-witness (set-r-1-a-inv-r-a6-1-witness p)))
                            (rot (a-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (a-inv-rotation (acl2-sqrt 2))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (set-r-1-a-inv-a5-1-witness p))
                            (rot (a-inv-rotation (acl2-sqrt 2))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-3)
                 )
           :in-theory nil
           ))
  )

(defthmd a-inv-diff-a-s2-d=>r-1-a-1-a5orr-1-a-1-r-a6-1
  (implies (and (m-= (m-* r-1 r-wit) p)
                (m-= (m-* a-inv a-inv-wit) r-wit))
           (m-= (m-* r-1 a-inv a-inv-wit) p)))

(defthmd a-inv-diff-a-s2-d=>r-1-a-1-a5orr-1-a-1-r-a6-2
  (implies (and (m-= (m-* r-1 a-inv-1 wa-1) p)
                (m-= (m-* r r-1) r0)
                (m-= r0 id)
                (m-= (m-* a-inv id) a-inv-1))
           (m-= (m-* r-1 a-inv r r-1 wa-1) p)))

(defthmd a-inv-diff-a-s2-d=>r-1-a-1-a5orr-1-a-1-r-a6
  (implies (r-1*a-inv*wa-01-or-wa-11 p)
           (or (set-r-1-a-inv-a5 p)
               (set-r-1-a-inv-r-a6 p)))
  :hints (("goal"
           :use ((:instance r-1*a-inv*wa-01-or-wa-11 (p p))
                 (:instance r-1*a-inv*wa-01-or-wa-11-1 (point p))
                 (:instance a-inv*wa-01-or-wa-11 (p (r-1*a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance a-inv*wa-01-or-wa-11-1 (point (r-1*a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance set-r-1-a-inv-a5 (p p))
                 (:instance set-r-1-a-inv-a5-1-suff (p (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p)))
                            (point p))
                 (:instance set-a5 (p (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p))))
                 (:instance a-inv-diff-a-s2-d=>r-1-a-1-a5orr-1-a-1-r-a6-1
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (r-wit (r-1*a-inv*wa-01-or-wa-11-1-witness p))
                            (p p)
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (a-inv-wit (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p))))
                 (:instance set-r-1-a-inv-r-a6 (p p))
                 (:instance set-r-1-a-inv-r-a6-1-suff
                            (point p)
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p)))))

                 (:instance set-a6 (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                            0 (* 2 (acl2-pi))))
                                                        (point-on-s2-not-d))
                                           (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p)))))
                 (:instance wa-11 (p (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p))))
                 (:instance wa-1 (p (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p))))

                 (:instance s2-d-p-equivalence-1
                            (p (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p))))
                 (:instance s2-d-p
                            (point (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p))))
                 (:instance s2-def-p
                            (point (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p)))
                            (rot (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance r3-rotationp (m (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                             0 (* 2 (acl2-pi))))
                                                         (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                            0 (* 2 (acl2-pi))))))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-4)

                 (:instance set-a6-1-suff
                            (point (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                         0 (* 2 (acl2-pi))))
                                                     (point-on-s2-not-d))
                                        (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p))))
                            (p (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p))))

                 (:instance a-inv-diff-a-s2-d=>r-1-a-1-a5orr-1-a-1-r-a6-2
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (a-inv-1 (a-inv-rotation (acl2-sqrt 2)))
                            (a-inv (a-inv-rotation (acl2-sqrt 2)))
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (wa-1 (a-inv*wa-01-or-wa-11-1-witness (r-1*a-inv*wa-01-or-wa-11-1-witness p)))
                            (r0 (rotation-3d 0 (point-on-s2-not-d)))
                            (id (id-rotation)))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-3)
                 (:instance r-theta-0=id (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 )
           :in-theory nil
           )))

(defthmd r-1-a-1-a5orr-1-a-1-r-a6-iff-a-inv-diff-a-s2-d
  (iff (r-1*a-inv*wa-01-or-wa-11 p)
       (or (set-r-1-a-inv-a5 p)
           (set-r-1-a-inv-r-a6 p)))
  :hints (("goal"
           :use ((:instance a-inv-diff-a-s2-d=>r-1-a-1-a5orr-1-a-1-r-a6)
                 (:instance r-1-a-1-a5orr-1-a-1-r-a6-=>-a-inv-diff-a-s2-d))
           )))

(defthmd r-1*s2-d-n-e=>r-1-a-1-a5or-r-1-a-1-r-a6-a8
  (implies (wit-inv*s2-d-p-n-set-e-p p)
           (or (set-r-1-a-inv-a5 p)
               (set-r-1-a-inv-r-a6 p)
               (set-a8 p)))
  :hints (("goal"
           :use ((:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 (:instance wit-inv*s2-d-p-n-set-e-1 (point p))
                 (:instance s2-d-p-n-set-e (point (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance s2-d-p-equivalence-2 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance a-inv*wa-01-or-wa-11-iff-a-inv-diff-a-s2-d
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1-a-1-a5orr-1-a-1-r-a6-iff-a-inv-diff-a-s2-d
                            (p p))
                 (:instance r-1*a-inv*wa-01-or-wa-11 (p p))
                 (:instance r-1*a-inv*wa-01-or-wa-11-1-suff
                            (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance set-a8 (p p))
                 (:instance r-1*wa-inv-1 (p p))
                 (:instance r-1*wa-inv-1-1-suff (p (wit-inv*s2-d-p-n-set-e-1-witness p)) (point p))
                 (:instance wa-inv-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd r-1-a-1-a5or-r-1-a-1-r-a6-a8=>r-1*s2-d-n-e
  (implies (or (set-r-1-a-inv-a5 p)
               (set-r-1-a-inv-r-a6 p)
               (set-a8 p))
           (wit-inv*s2-d-p-n-set-e-p p))
  :hints (("goal"
           :use ((:instance r-1-a-1-a5orr-1-a-1-r-a6-iff-a-inv-diff-a-s2-d (p p))
                 (:instance set-a8 (p p))
                 (:instance r-1*wa-inv-1 (p p))
                 (:instance r-1*wa-inv-1-1 (point p))
                 (:instance wa-inv-1 (p (r-1*wa-inv-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff
                            (point p)
                            (p (r-1*wa-inv-1-1-witness p)))
                 (:instance s2-d-p-equivalence-2 (p (r-1*wa-inv-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wa-inv-1-1-witness p)))
                 (:instance r-1*a-inv*wa-01-or-wa-11 (p p))
                 (:instance r-1*a-inv*wa-01-or-wa-11-1 (point p))
                 (:instance a-inv*wa-01-or-wa-11-iff-a-inv-diff-a-s2-d
                            (p (r-1*a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance s2-d-p-equivalence-2 (p (r-1*a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*a-inv*wa-01-or-wa-11-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff
                            (point p)
                            (p (r-1*a-inv*wa-01-or-wa-11-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd r-1-a-1-a5or-r-1-a-1-r-a6-a8-iff-r-1*s2-d-n-e
  (iff (or (set-r-1-a-inv-a5 p)
           (set-r-1-a-inv-r-a6 p)
           (set-a8 p))
       (wit-inv*s2-d-p-n-set-e-p p))
  :hints (("goal"
           :use ((:instance r-1-a-1-a5or-r-1-a-1-r-a6-a8=>r-1*s2-d-n-e)
                 (:instance r-1*s2-d-n-e=>r-1-a-1-a5or-r-1-a-1-r-a6-a8))
           )))

(defthmd a-1-a3ora-1-r-a4-iff-a-inv-diff-a-s2-d
  (iff (or (set-a-inv-a3 p)
           (set-a-inv-r-a4 p))
       (and (a-inv-diff-a-s2-d-p p)
            (s2-not-e p)))
  :hints (("goal"
           :use ((:instance a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4))
           )))

(defthmd s2-e-iff-a-1-a3-or-a-1-r-a4-a7
  (iff (s2-not-d-n-s2-not-e p)
       (or (set-a-inv-a3 p)
           (set-a-inv-r-a4 p)
           (set-a7 p)))
  :hints (("goal"
           :use ((:instance s2-not-d-n-s2-not-e (point p))
                 (:instance s2-d-p-equivalence-2 (p p))
                 (:instance wa-inv-0 (p p))
                 (:instance set-a7 (p p))
                 (:instance a-1-a3ora-1-r-a4-iff-a-inv-diff-a-s2-d (p p))
                 )
           :in-theory nil
           )))

(defun-sk set-b-inv-a9-1 (point)
  (exists p
          (and (set-a9 p)
               (m-= (m-* (b-inv-rotation (acl2-sqrt 2)) p)
                    point))))

(defun set-b-inv-a9 (p)
  (and (point-in-r3 p)
       (set-b-inv-a9-1 p)))

(defun-sk set-b-inv-r-a10-1 (point)
  (exists p
          (and (set-a10 p)
               (m-= (m-* (b-inv-rotation (acl2-sqrt 2))
                         (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                         p)
                    point))))

(defun set-b-inv-r-a10 (p)
  (and (point-in-r3 p)
       (set-b-inv-r-a10-1 p)))

(defun-sk set-r-1-b-inv-a11-1 (point)
  (exists p
          (and (set-a11 p)
               (m-= (m-*
                     (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                     (b-inv-rotation (acl2-sqrt 2))
                     p)
                    point))))

(defun set-r-1-b-inv-a11 (p)
  (and (point-in-r3 p)
       (set-r-1-b-inv-a11-1 p)))

(defun-sk set-r-1-b-inv-r-a12-1 (point)
  (exists p
          (and (set-a12 p)
               (m-= (m-*
                     (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                     (b-inv-rotation (acl2-sqrt 2))
                     (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                     p)
                    point))))

(defun set-r-1-b-inv-r-a12 (p)
  (and (point-in-r3 p)
       (set-r-1-b-inv-r-a12-1 p)))

(defthmd b-inv-diff-b-s2-d=>rot-b*s2-not-e-1
  (m-= (rotation (list (wb-inv)) (acl2-sqrt 2))
       (b-inv-rotation (acl2-sqrt 2)))
  :hints (("goal"
           :use ((:instance wb-inv)
                 (:instance wb)
                 (:instance wa)
                 (:instance wa-inv)
                 (:instance rotation (w '(#\d)) (x (acl2-sqrt 2)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m*id=m (m1 (b-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (b-inv-rotation (acl2-sqrt 2))))
                 )
           :in-theory nil
           ))
  )

(defthmd b-inv-diff-b-s2-d=>rot-b*s2-not-e
  (implies (and (b-inv-diff-b-s2-d-p p)
                (s2-not-e p))
           (rot-b*s2-not-e (b-inv-diff-b-s2-d-p-1-witness p)))
  :hints (("goal"
           :use ((:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance rot-b*s2-not-e (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance rot-b*s2-not-e-1-suff (point (b-inv-diff-b-s2-d-p-1-witness p))
                            (p p))
                 (:instance b-inv-diff-b-s2-d=>rot-b*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-2
                            (rot-lwa-inv (rotation (list (wb-inv)) (acl2-sqrt 2)))
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (wit (b-inv-diff-b-s2-d-p-1-witness p))
                            (wit1 (b-inv-diff-b-s2-d-p-1-witness p))
                            (id (id-rotation))
                            (a (b-rotation (acl2-sqrt 2)))
                            (p p))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (b-inv-diff-b-s2-d-p-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd b-inv-diff-b-s2-d=>wb-00-orwb-10-wit
  (implies (and (b-inv-diff-b-s2-d-p p)
                (s2-not-e p))
           (or (wb-00 (b-inv-diff-b-s2-d-p-1-witness p))
               (wb-10 (b-inv-diff-b-s2-d-p-1-witness p))))
  :hints (("goal"
           :use ((:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-00 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-10 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-0 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-not-e (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance rot-b*s2-not-e (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance rot-b*s2-not-e-1 (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance b-inv-diff-b-s2-d=>rot-b*s2-not-e (p p))
                 )
           :in-theory nil
           ))
  )

(defthmd b-inv-diff-b-s2-d=>b-1-a9orb-1-r-a10
  (implies (and (b-inv-diff-b-s2-d-p p)
                (s2-not-e p))
           (or (set-b-inv-a9 p)
               (set-b-inv-r-a10 p)))
  :hints (("goal"
           :use ((:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1 (p p))
                 (:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1 (p p))
                 (:instance wb-00 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-10 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-0 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-not-e (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p-equivalence-2 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance b-inv-diff-b-s2-d=>wb-00-orwb-10-wit (p p))
                 (:instance set-b-inv-a9 (p p))
                 (:instance set-b-inv-a9-1-suff (point p) (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance set-a9 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance b-inv-diff-b-s2-d=>rot-b*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-1
                            (rotl-a-inv (rotation (list (wb-inv)) (acl2-sqrt 2)))
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (wit (b-inv-diff-b-s2-d-p-1-witness p))
                            (p p))

                 (:instance set-a10
                            (p (m-*
                                (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                (b-inv-diff-b-s2-d-p-1-witness p))))
                 (:instance set-a10-1-suff
                            (point (m-*
                                    (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (b-inv-diff-b-s2-d-p-1-witness p)))
                            (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance set-b-inv-r-a10 (p p))
                 (:instance set-b-inv-r-a10-1-suff (point p)
                            (p (m-*
                                (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                (b-inv-diff-b-s2-d-p-1-witness p))))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-2
                            (p p)
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (a-inv-1 (b-inv-rotation (acl2-sqrt 2)))
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (id (id-rotation))
                            (wit-0 (rotation-3d 0 (point-on-s2-not-d)))
                            (wit (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-3)
                 (:instance r-theta-0=id
                            (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b-inv-diff-b-s2-d-p-1-witness p))
                            (rot (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp
                            (m (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                0 (* 2 (acl2-pi))))
                                            (point-on-s2-not-d))))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-4)
                 )
           :in-theory nil
           )
          ))

(defun-sk b-inv*wb-00-or-wb-10-1 (point)
  (exists p
          (and (or (wb-00 p)
                   (wb-10 p))
               (m-= (m-* (b-inv-rotation (acl2-sqrt 2)) p)
                    point))))

(defun b-inv*wb-00-or-wb-10 (p)
  (and (point-in-r3 p)
       (b-inv*wb-00-or-wb-10-1 p)))

(defthmd b-1-a9orb-1-r-a10=>b-inv-diff-b-s2-d-2
  (implies (or (set-b-inv-a9 p)
               (set-b-inv-r-a10 p))
           (b-inv*wb-00-or-wb-10 p))
  :hints (("goal"
           :cases ((set-b-inv-a9 p)
                   (set-b-inv-r-a10 p))
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance set-b-inv-a9 (p p))
                 (:instance set-b-inv-a9-1 (point p))
                 (:instance set-a9 (p (set-b-inv-a9-1-witness p)))
                 (:instance b-inv*wb-00-or-wb-10-1-suff (point p)
                            (p (set-b-inv-a9-1-witness p)))
                 (:instance b-inv*wb-00-or-wb-10 (p p))
                 )
           )
          ("subgoal 1"
           :use ((:instance set-b-inv-r-a10 (p p))
                 (:instance set-b-inv-r-a10-1 (point p))
                 (:instance set-a10 (p (set-b-inv-r-a10-1-witness p)))
                 (:instance set-a10-1 (point (set-b-inv-r-a10-1-witness p)))
                 (:instance b-inv*wb-00-or-wb-10-1-suff (point p)
                            (p (set-a10-1-witness (set-b-inv-r-a10-1-witness p))))
                 (:instance a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d-1
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (a-inv-1 (b-inv-rotation (acl2-sqrt 2)))
                            (r-wit (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi)))
                                                (point-on-s2-not-d)))
                            (wit (set-b-inv-r-a10-1-witness p))
                            (p p)
                            (r-1-wit (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                      0 (* 2 (acl2-pi))))
                                                  (point-on-s2-not-d)))
                            (wit-wit (set-a10-1-witness (set-b-inv-r-a10-1-witness p)))
                            (id (id-rotation))
                            )
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-3)
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance r-theta-0=id (u (point-on-s2-not-d)))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance b-inv*wb-00-or-wb-10 (p p))
                 )
           )
          ))

(defthmd b-1-a9orb-1-r-a10=>b-inv-diff-b-s2-d
  (implies (or (set-b-inv-a9 p)
               (set-b-inv-r-a10 p))
           (and (b-inv-diff-b-s2-d-p p)
                (s2-not-e p)))
  :hints (("goal"
           :use ((:instance b-1-a9orb-1-r-a10=>b-inv-diff-b-s2-d-2 (p p))
                 (:instance b-inv*wb-00-or-wb-10 (p p))
                 (:instance b-inv*wb-00-or-wb-10-1 (point p))
                 (:instance wb-00 (p (b-inv*wb-00-or-wb-10-1-witness p)))
                 (:instance wb-10 (p (b-inv*wb-00-or-wb-10-1-witness p)))
                 (:instance wb-0 (p (b-inv*wb-00-or-wb-10-1-witness p)))
                 (:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1-suff (p p)
                            (p1 (b-inv*wb-00-or-wb-10-1-witness p)))
                 (:instance b-inv-diff-b-s2-d=>rot-b*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-1
                            (rotl-a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (a-inv (rotation (list (wb-inv)) (acl2-sqrt 2)))
                            (wit (b-inv*wb-00-or-wb-10-1-witness p))
                            (p p))
                 (:instance rot-b*s2-not-e (p (b-inv*wb-00-or-wb-10-1-witness p)))
                 (:instance rot-b*s2-not-e-1 (point (b-inv*wb-00-or-wb-10-1-witness p)))
                 (:instance a-1-a3ora-1-r-a4=>a-inv-diff-a-s2-d-3
                            (a-rot (b-rotation (acl2-sqrt 2)))
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (wit-wit (rot-b*s2-not-e-1-witness (b-inv*wb-00-or-wb-10-1-witness p)))
                            (wit-wit1 (rot-b*s2-not-e-1-witness (b-inv*wb-00-or-wb-10-1-witness p)))
                            (wit (b-inv*wb-00-or-wb-10-1-witness p))
                            (p p)
                            (id (id-rotation)))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance s2-not-e (point (rot-b*s2-not-e-1-witness (b-inv*wb-00-or-wb-10-1-witness p))))
                 (:instance s2-def-p (point (rot-b*s2-not-e-1-witness (b-inv*wb-00-or-wb-10-1-witness p))))
                 (:instance m-*point-id=point (p1 (rot-b*s2-not-e-1-witness (b-inv*wb-00-or-wb-10-1-witness p))))
                 (:instance p1=p2-n-s2-e-p1=>s2-e-p2 (p1 (rot-b*s2-not-e-1-witness (b-inv*wb-00-or-wb-10-1-witness p)))
                            (p2 p))
                 (:instance wb-1 (p (b-inv*wb-00-or-wb-10-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd b-1-a9orb-1-r-a10-iff-b-inv-diff-b-s2-d
  (iff (or (set-b-inv-a9 p)
           (set-b-inv-r-a10 p))
       (and (b-inv-diff-b-s2-d-p p)
            (s2-not-e p)))
  :hints (("goal"
           :use ((:instance b-1-a9orb-1-r-a10=>b-inv-diff-b-s2-d)
                 (:instance b-inv-diff-b-s2-d=>b-1-a9orb-1-r-a10))
           )))

(defthmd b-inv-diff-b-s2-d=>rot-b*-e
  (implies (and (b-inv-diff-b-s2-d-p p)
                (set-e-p p))
           (rot-b*-e (b-inv-diff-b-s2-d-p-1-witness p)))
  :hints (("goal"
           :use ((:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance rot-b*-e (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance rot-b*-e-1-suff (point (b-inv-diff-b-s2-d-p-1-witness p))
                            (p p))
                 (:instance b-inv-diff-b-s2-d=>rot-b*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>rot-a*s2-not-e-2
                            (rot-lwa-inv (rotation (list (wb-inv)) (acl2-sqrt 2)))
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (wit (b-inv-diff-b-s2-d-p-1-witness p))
                            (wit1 (b-inv-diff-b-s2-d-p-1-witness p))
                            (id (id-rotation))
                            (a (b-rotation (acl2-sqrt 2)))
                            (p p))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (b-inv-diff-b-s2-d-p-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd b-inv-diff-b-s2-d=>wb-01-orwb-11-wit
  (implies (and (b-inv-diff-b-s2-d-p p)
                (set-e-p p))
           (or (wb-01 (b-inv-diff-b-s2-d-p-1-witness p))
               (wb-11 (b-inv-diff-b-s2-d-p-1-witness p))))
  :hints (("goal"
           :use ((:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1 (p p))
                 (:instance s2-d-p-equivalence-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-01 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-11 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-0 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-not-e (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance rot-b*-e (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance rot-b*-e-1 (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance b-inv-diff-b-s2-d=>rot-b*-e (p p))
                 )
           :in-theory nil
           ))
  )

(defun-sk b-inv*wb-01-or-wb-11-1 (point)
  (exists p
          (and (or (wb-01 p)
                   (wb-11 p))
               (m-= (m-* (b-inv-rotation (acl2-sqrt 2)) p)
                    point))))

(defun b-inv*wb-01-or-wb-11 (p)
  (and (point-in-r3 p)
       (b-inv*wb-01-or-wb-11-1 p)))

(defthmd b-inv-diff-b-s2-d=>b-inv*wb-01-or-wb-11
  (implies (and (b-inv-diff-b-s2-d-p p)
                (set-e-p p))
           (b-inv*wb-01-or-wb-11 p))
  :hints (("goal"
           :use ((:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1 (p p))
                 (:instance wb-01 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-11 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-0 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance wb-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-not-e (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p-equivalence-2 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p-equivalence-1 (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-d-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance s2-def-p (point (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance b-inv-diff-b-s2-d=>wb-01-orwb-11-wit (p p))
                 (:instance b-inv*wb-01-or-wb-11 (p p))
                 (:instance b-inv*wb-01-or-wb-11-1-suff (point p) (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance b-inv-diff-b-s2-d=>rot-b*s2-not-e-1)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-1
                            (rotl-a-inv (rotation (list (wb-inv)) (acl2-sqrt 2)))
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (wit (b-inv-diff-b-s2-d-p-1-witness p))
                            (p p))
                 )
           :in-theory nil
           )
          ))

(defthmd b-inv*wb-01-or-wb-11=>b-inv-diff-b-s2-d
  (implies (b-inv*wb-01-or-wb-11 p)
           (and (b-inv-diff-b-s2-d-p p)
                (set-e-p p)))
  :hints (("goal"
           :use ((:instance b-inv*wb-01-or-wb-11 (p p))
                 (:instance b-inv*wb-01-or-wb-11-1 (point p))
                 (:instance wb-01 (p (b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance wb-0 (p (b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance wb-11 (p (b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance wb-1 (p (b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance rot-b*-e (p (b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance rot-b*-e-1 (point (b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1-suff (p1 (b-inv*wb-01-or-wb-11-1-witness p)) (p p))
                 (:instance b-inv-diff-b-s2-d=>rot-b*s2-not-e-1)
                 (:instance a-inv*wa-01-or-wa-11=>a-inv-diff-a-s2-d-1
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (wa (b-inv*wb-01-or-wb-11-1-witness p))
                            (p p)
                            (rot-a-inv (rotation (list (wb-inv)) (acl2-sqrt 2))))
                 (:instance a-inv*wa-01-or-wa-11=>a-inv-diff-a-s2-d-2
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (wa-0111 (b-inv*wb-01-or-wb-11-1-witness p))
                            (p p)
                            (a (b-rotation (acl2-sqrt 2)))
                            (rot-wit (rot-b*-e-1-witness (b-inv*wb-01-or-wb-11-1-witness p)))
                            (id (id-rotation))
                            (rot-wit1 (rot-b*-e-1-witness (b-inv*wb-01-or-wb-11-1-witness p)))
                            )
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance set-e-p=>s2-def-p (point (rot-b*-e-1-witness (b-inv*wb-01-or-wb-11-1-witness p))))
                 (:instance s2-def-p (point (rot-b*-e-1-witness (b-inv*wb-01-or-wb-11-1-witness p))))
                 (:instance m-*point-id=point (p1 (rot-b*-e-1-witness (b-inv*wb-01-or-wb-11-1-witness p))))
                 (:instance p1=p2-n-e-p1=>e-p2 (p1 (rot-b*-e-1-witness (b-inv*wb-01-or-wb-11-1-witness p)))
                            (p2 p))
                 )
           :in-theory nil
           )))

(defthmd b-inv*wb-01-or-wb-11-iff-b-inv-diff-b-s2-d
  (iff (b-inv*wb-01-or-wb-11 p)
       (and (b-inv-diff-b-s2-d-p p)
            (set-e-p p)))
  :hints (("goal"
           :use ((:instance b-inv*wb-01-or-wb-11=>b-inv-diff-b-s2-d)
                 (:instance b-inv-diff-b-s2-d=>b-inv*wb-01-or-wb-11))
           )))

(defun-sk r-1*b-inv*wb-01-or-wb-11-1 (point)
  (exists p
          (and (b-inv*wb-01-or-wb-11 p)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                          0 (* 2 (acl2-pi))))
                                      (point-on-s2-not-d))
                         p)
                    point))))

(defun r-1*b-inv*wb-01-or-wb-11 (p)
  (and (point-in-r3 p)
       (r-1*b-inv*wb-01-or-wb-11-1 p)))

(defthmd r-1-b-1-a11orr-1-b-1-r-a12-=>-b-inv-diff-b-s2-d
  (implies (or (set-r-1-b-inv-a11 p)
               (set-r-1-b-inv-r-a12 p))
           (r-1*b-inv*wb-01-or-wb-11 p))
  :hints (("goal"
           :use ((:instance set-r-1-b-inv-a11 (p p))
                 (:instance set-r-1-b-inv-a11-1 (point p))
                 (:instance set-a11 (p (set-r-1-b-inv-a11-1-witness p)))
                 (:instance r-1*b-inv*wb-01-or-wb-11 (p p))
                 (:instance r-1*b-inv*wb-01-or-wb-11-1-suff
                            (p (m-* (b-inv-rotation (acl2-sqrt 2))
                                    (set-r-1-b-inv-a11-1-witness p)))
                            (point p))
                 (:instance b-inv*wb-01-or-wb-11
                            (p (m-* (b-inv-rotation (acl2-sqrt 2))
                                    (set-r-1-b-inv-a11-1-witness p))))
                 (:instance b-inv*wb-01-or-wb-11-1-suff
                            (point (m-* (b-inv-rotation (acl2-sqrt 2))
                                        (set-r-1-b-inv-a11-1-witness p)))
                            (p (set-r-1-b-inv-a11-1-witness p)))
                 (:instance wb-01 (p (set-r-1-b-inv-a11-1-witness p)))
                 (:instance wb-0 (p (set-r-1-b-inv-a11-1-witness p)))
                 (:instance s2-not-e (point (set-r-1-b-inv-a11-1-witness p)))
                 (:instance s2-def-p (point (set-r-1-b-inv-a11-1-witness p)))
                 (:instance set-r-1-b-inv-r-a12 (p p))
                 (:instance set-r-1-b-inv-r-a12-1 (point p))
                 (:instance set-a12 (p (set-r-1-b-inv-r-a12-1-witness p)))
                 (:instance set-a12-1 (point (set-r-1-b-inv-r-a12-1-witness p)))
                 (:instance r-1*b-inv*wb-01-or-wb-11 (p p))
                 (:instance r-1*b-inv*wb-01-or-wb-11-1-suff
                            (p (m-* (b-inv-rotation (acl2-sqrt 2))
                                    (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                            (point p))
                 (:instance b-inv*wb-01-or-wb-11
                            (p (m-* (b-inv-rotation (acl2-sqrt 2))
                                    (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p)))))
                 (:instance b-inv*wb-01-or-wb-11-1-suff
                            (point (m-* (b-inv-rotation (acl2-sqrt 2))
                                        (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                            (p (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance r-1-a-1-a5orr-1-a-1-r-a6-iff-a-inv-diff-a-s2-d-1
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (w11 (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p)))
                            (wit (set-r-1-b-inv-r-a12-1-witness p))
                            (p p)
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (r0 (rotation-3d 0 (point-on-s2-not-d)))
                            (id (id-rotation))
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (a-inv1 (b-inv-rotation (acl2-sqrt 2))))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance r-theta-0=id (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance wb-01 (p (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance wb-11 (p (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance wb-0 (p (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance wb-1 (p (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance s2-d-p-equivalence-1 (p (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance s2-d-p (point (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance s2-def-p (point (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (set-a12-1-witness (set-r-1-b-inv-r-a12-1-witness p)))
                            (rot (b-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (b-inv-rotation (acl2-sqrt 2))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (set-r-1-b-inv-a11-1-witness p))
                            (rot (b-inv-rotation (acl2-sqrt 2))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-3)
                 )
           :in-theory nil
           ))
  )

(defthmd b-inv-diff-b-s2-d=>r-1-b-1-a11orr-1-b-1-r-a12
  (implies (r-1*b-inv*wb-01-or-wb-11 p)
           (or (set-r-1-b-inv-a11 p)
               (set-r-1-b-inv-r-a12 p)))
  :hints (("goal"
           :use ((:instance r-1*b-inv*wb-01-or-wb-11 (p p))
                 (:instance r-1*b-inv*wb-01-or-wb-11-1 (point p))
                 (:instance b-inv*wb-01-or-wb-11 (p (r-1*b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance b-inv*wb-01-or-wb-11-1 (point (r-1*b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance set-r-1-b-inv-a11 (p p))
                 (:instance set-r-1-b-inv-a11-1-suff (p (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p)))
                            (point p))
                 (:instance set-a11 (p (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p))))
                 (:instance a-inv-diff-a-s2-d=>r-1-a-1-a5orr-1-a-1-r-a6-1
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (r-wit (r-1*b-inv*wb-01-or-wb-11-1-witness p))
                            (p p)
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (a-inv-wit (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p))))
                 (:instance set-r-1-b-inv-r-a12 (p p))
                 (:instance set-r-1-b-inv-r-a12-1-suff
                            (point p)
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p)))))

                 (:instance set-a12 (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                             0 (* 2 (acl2-pi))))
                                                         (point-on-s2-not-d))
                                            (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p)))))
                 (:instance wb-11 (p (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p))))
                 (:instance wb-1 (p (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p))))

                 (:instance s2-d-p-equivalence-1
                            (p (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p))))
                 (:instance s2-d-p
                            (point (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p))))
                 (:instance s2-def-p
                            (point (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p)))
                            (rot (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance r3-rotationp (m (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                             0 (* 2 (acl2-pi))))
                                                         (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                            0 (* 2 (acl2-pi))))))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-4)

                 (:instance set-a12-1-suff
                            (point (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                         0 (* 2 (acl2-pi))))
                                                     (point-on-s2-not-d))
                                        (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p))))
                            (p (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p))))

                 (:instance a-inv-diff-a-s2-d=>r-1-a-1-a5orr-1-a-1-r-a6-2
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (a-inv-1 (b-inv-rotation (acl2-sqrt 2)))
                            (a-inv (b-inv-rotation (acl2-sqrt 2)))
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (wa-1 (b-inv*wb-01-or-wb-11-1-witness (r-1*b-inv*wb-01-or-wb-11-1-witness p)))
                            (r0 (rotation-3d 0 (point-on-s2-not-d)))
                            (id (id-rotation)))
                 (:instance a-inv-diff-a-s2-d=>a-1-a3ora-1-r-a4-3)
                 (:instance r-theta-0=id (u (point-on-s2-not-d)))
                 (:instance exists-point-on-s2-not-d-2)
                 (:instance s2-def-p (point (point-on-s2-not-d)))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 )
           :in-theory nil
           )))

(defthmd r-1-b-1-a11orr-1-b-1-r-a12-iff-b-inv-diff-b-s2-d
  (iff (r-1*b-inv*wb-01-or-wb-11 p)
       (or (set-r-1-b-inv-a11 p)
           (set-r-1-b-inv-r-a12 p)))
  :hints (("goal"
           :use ((:instance b-inv-diff-b-s2-d=>r-1-b-1-a11orr-1-b-1-r-a12)
                 (:instance r-1-b-1-a11orr-1-b-1-r-a12-=>-b-inv-diff-b-s2-d))
           )))

(defthmd r-1*s2-d-n-e=>r-1-b-1-a11or-r-1-b-1-r-a12-a14
  (implies (wit-inv*s2-d-p-n-set-e-p p)
           (or (set-r-1-b-inv-a11 p)
               (set-r-1-b-inv-r-a12 p)
               (set-a14 p)))
  :hints (("goal"
           :use ((:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 (:instance wit-inv*s2-d-p-n-set-e-1 (point p))
                 (:instance s2-d-p-n-set-e (point (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance s2-d-p-equivalence-3 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance b-inv*wb-01-or-wb-11-iff-b-inv-diff-b-s2-d
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance r-1-b-1-a11orr-1-b-1-r-a12-iff-b-inv-diff-b-s2-d
                            (p p))
                 (:instance r-1*b-inv*wb-01-or-wb-11 (p p))
                 (:instance r-1*b-inv*wb-01-or-wb-11-1-suff
                            (point p)
                            (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 (:instance set-a14 (p p))
                 (:instance r-1*wb-inv-1 (p p))
                 (:instance r-1*wb-inv-1-1-suff (p (wit-inv*s2-d-p-n-set-e-1-witness p)) (point p))
                 (:instance wb-inv-1 (p (wit-inv*s2-d-p-n-set-e-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd r-1-b-1-a11or-r-1-b-1-r-a12-a14=>r-1*s2-d-n-e
  (implies (or (set-r-1-b-inv-a11 p)
               (set-r-1-b-inv-r-a12 p)
               (set-a14 p))
           (wit-inv*s2-d-p-n-set-e-p p))
  :hints (("goal"
           :use ((:instance r-1-b-1-a11orr-1-b-1-r-a12-iff-b-inv-diff-b-s2-d (p p))
                 (:instance set-a14 (p p))
                 (:instance r-1*wb-inv-1 (p p))
                 (:instance r-1*wb-inv-1-1 (point p))
                 (:instance wb-inv-1 (p (r-1*wb-inv-1-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff
                            (point p)
                            (p (r-1*wb-inv-1-1-witness p)))
                 (:instance s2-d-p-equivalence-3 (p (r-1*wb-inv-1-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*wb-inv-1-1-witness p)))
                 (:instance r-1*b-inv*wb-01-or-wb-11 (p p))
                 (:instance r-1*b-inv*wb-01-or-wb-11-1 (point p))
                 (:instance b-inv*wb-01-or-wb-11-iff-b-inv-diff-b-s2-d
                            (p (r-1*b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance s2-d-p-equivalence-3 (p (r-1*b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance s2-d-p-n-set-e (point (r-1*b-inv*wb-01-or-wb-11-1-witness p)))
                 (:instance wit-inv*s2-d-p-n-set-e-p (point p))
                 (:instance wit-inv*s2-d-p-n-set-e-1-suff
                            (point p)
                            (p (r-1*b-inv*wb-01-or-wb-11-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd r-1-b-1-a11or-r-1-b-1-r-a12-a14-iff-r-1*s2-d-n-e
  (iff (or (set-r-1-b-inv-a11 p)
           (set-r-1-b-inv-r-a12 p)
           (set-a14 p))
       (wit-inv*s2-d-p-n-set-e-p p))
  :hints (("goal"
           :use ((:instance r-1-b-1-a11or-r-1-b-1-r-a12-a14=>r-1*s2-d-n-e)
                 (:instance r-1*s2-d-n-e=>r-1-b-1-a11or-r-1-b-1-r-a12-a14))
           )))

(defthmd b-1-a9orb-1-r-a10-iff-b-inv-diff-b-s2-d
  (iff (or (set-b-inv-a9 p)
           (set-b-inv-r-a10 p))
       (and (b-inv-diff-b-s2-d-p p)
            (s2-not-e p)))
  :hints (("goal"
           :use ((:instance b-1-a9orb-1-r-a10=>b-inv-diff-b-s2-d)
                 (:instance b-inv-diff-b-s2-d=>b-1-a9orb-1-r-a10))
           )))

(defthmd s2-e-iff-b-1-a9-or-b-1-r-a10-a13
  (iff (s2-not-d-n-s2-not-e p)
       (or (set-b-inv-a9 p)
           (set-b-inv-r-a10 p)
           (set-a13 p)))
  :hints (("goal"
           :use ((:instance s2-not-d-n-s2-not-e (point p))
                 (:instance s2-d-p-equivalence-3 (p p))
                 (:instance wb-inv-0 (p p))
                 (:instance set-a13 (p p))
                 (:instance b-1-a9orb-1-r-a10-iff-b-inv-diff-b-s2-d (p p))
                 )
           :in-theory nil
           )))

(defthmd s2-equiv-1
  (iff (s2-def-p p)
       (or (set-a1 p)
           (set-a2 p)
           (set-a3 p)
           (set-a4 p)
           (set-a5 p)
           (set-a6 p)
           (set-a7 p)
           (set-a8 p)
           (set-a9 p)
           (set-a10 p)
           (set-a11 p)
           (set-a12 p)
           (set-a13 p)
           (set-a14 p)))
  :hints (("goal"
           :use ((:instance r-1-setas-iff-r-1-diff (p p))
                 (:instance s2-iff-diff-s2 (p p))
                 (:instance r-1-diff-s2 (p p))
                 (:instance r-1-setas (p p))
                 (:instance diff-s2 (p p))
                 (:instance set-a1 (p p))
                 (:instance set-a3 (p p))
                 (:instance set-a5 (p p))
                 (:instance set-a7 (p p))
                 (:instance wa-0-iff-wa00-or-wa01 (p p))
                 (:instance wb-0-iff-wb00-or-wb01 (p p))
                 (:instance set-a9 (p p))
                 (:instance set-a11 (p p))
                 (:instance set-a13 (p p))
                 )
           :in-theory nil
           )))

(defthmd s2-equiv-2
  (iff (s2-def-p p)
       (or (set-a-inv-a3 p)
           (set-a-inv-r-a4 p)
           (set-r-1-a-inv-a5 p)
           (set-r-1-a-inv-r-a6 p)
           (set-a7 p)
           (set-a8 p)))
  :hints (("goal"
           :use ((:instance iff-s2-s2-e-or-witinv*s2-d-n-e (point p))
                 (:instance s2-e-iff-a-1-a3-or-a-1-r-a4-a7 (p p))
                 (:instance r-1-a-1-a5or-r-1-a-1-r-a6-a8-iff-r-1*s2-d-n-e (p p))
                 )
           :in-theory nil
           )))

(defthmd s2-equiv-3
  (iff (s2-def-p p)
       (or (set-b-inv-a9 p)
           (set-b-inv-r-a10 p)
           (set-r-1-b-inv-a11 p)
           (set-r-1-b-inv-r-a12 p)
           (set-a13 p)
           (set-a14 p)))
  :hints (("goal"
           :use ((:instance iff-s2-s2-e-or-witinv*s2-d-n-e (point p))
                 (:instance s2-e-iff-b-1-a9-or-b-1-r-a10-a13 (p p))
                 (:instance r-1-b-1-a11or-r-1-b-1-r-a12-a14-iff-r-1*s2-d-n-e (p p))
                 )
           :in-theory nil
           )))
