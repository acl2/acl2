; Banach-Tarski theorem
;
; Proof of Hausdorff paradox.
; Book contains the proof of equivalence between different partitions of S^2-D.
; See hausdorff-paradox-2.lisp for the proof that the set D is countable.
;
;
; Copyright (C) 2021 University of Wyoming
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Main Authors: Jagadish Bapanapally (jagadishb285@gmail.com)
;
; Contributing Authors:
;   Ruben Gamboa (ruben@uwyo.edu)

(in-package "ACL2")

; cert_param: (uses-acl2r)

(include-book "rotations")

(defun point-in-r3 (x)
  (and (array2p :fake-name x)
       (equal (car (dimensions :fake-name x)) 3)
       (equal (cadr (dimensions :fake-name x)) 1)
       (realp (aref2 :fake-name x 0 0))
       (realp (aref2 :fake-name x 1 0))
       (realp (aref2 :fake-name x 2 0))))

(defthm m-*point1^t-point1
  (implies (point-in-r3 x)
           (equal (aref2 :fake-name (m-* (m-trans x) x) 0 0)
                  (+ (* (aref2 :fake-name x 0 0) (aref2 :fake-name x 0 0))
                     (* (aref2 :fake-name x 1 0) (aref2 :fake-name x 1 0))
                     (* (aref2 :fake-name x 2 0) (aref2 :fake-name x 2 0)))))
  :hints (("goal"
           :use (:instance point-in-r3 (x x))
           :do-not-induct t
           )))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm m-*point-id=point
    (implies (point-in-r3 p1)
             (m-= (m-* (id-rotation) p1) p1))
    :hints (("goal"
             :use (:instance point-in-r3 (x p1))
             :in-theory (e/d (m-* m-= alist2p dimensions header aref2) ())
             :do-not-induct t
             )))
  )

(encapsulate
  ()

  (local
   (defthm rotation*point-on-s2-1
     (implies (and (array2p :fake-name p1)
                   (array2p :fake-name p2)
                   (equal (car (dimensions :fake-name p1)) 1)
                   (equal (cadr (dimensions :fake-name p1)) 1)
                   (realp (aref2 :fake-name p1 0 0))
                   (realp (aref2 :fake-name p2 0 0))
                   (m-= p1 p2))
              (equal (aref2 :fake-name p1 0 0)
                     (aref2 :fake-name p2 0 0)))
     :hints (("goal"
              :in-theory (enable m-= dimensions)
              ))))

  (defthm rotation*point-on-s2-2
    (implies (r3-matrixp m1)
             (m-= (m-* m1 (id-rotation)) m1))
    :hints (("goal"
             :use ((:instance right-unity-of-m-1-for-m-* (m1 m1) (name :fake-name))
                   (:instance normalize-dimensions-name (name '$arg) (l m1))
                   (:instance array2p-alist2p-fname (l m1)))
             :in-theory (e/d (header dimensions default m-*) ())
             )))

  (local
   (defthm rotation*point-on-s2-3
     (implies (and (array2p :fake-name a)
                   (array2p :fake-name b)
                   (array2p :fake-name c)
                   (array2p :fake-name x)
                   (m-= b x))
              (equal (m-* a b c) (m-* a x c)))))

  (local
   (defthm rotation*point-on-s2-4
     (implies (and (point-in-r3 p1)
                   (r3-rotationp rot))
              (equal (m-* (m-trans (m-* rot p1)) (m-* rot p1))
                     (m-* (m-trans p1) (m-trans rot) rot p1)))
     :hints (("goal"
              :use ((:instance m-trans-m-*=m-*-m-trans (m1 rot) (m2 p1) (name :fake-name)))
              :in-theory (e/d () (rotation*point-on-s2-3))))))

  (local
   (defthm rotation*point-on-s2-5
     (implies (and (array2p :fake-name m1)
                   (array2p :fake-name m2)
                   (array2p :fake-name m3)
                   (array2p :fake-name m4))
              (equal (m-* m1 m2 m3 m4) (m-* m1 (m-* m2 m3) m4)))
     :hints (("goal"
              :in-theory (e/d () (rotation*point-on-s2-3))
              ))))

  (local
   (defthm rotation*point-on-s2-6
     (implies (point-in-r3 p1)
              (array2p :fake-name (m-trans p1)))))

  (local
   (defthm rotation*point-on-s2-7
     (implies (and (point-in-r3 p1)
                   (r3-rotationp rot))
              (m-= (m-* (m-trans (m-* rot p1)) (m-* rot p1))
                   (m-* (m-trans p1) p1)))
     :hints (("goal"
              :use ((:instance rotation*point-on-s2-4 (p1 p1) (rot rot))
                    (:instance rotation*point-on-s2-5 (m1 (m-trans p1)) (m2 (m-trans rot)) (m3 rot) (m4 p1))
                    (:instance r3-rotationp (m rot))
                    (:instance m-*-m-inverse-m (m rot))
                    (:instance rotation*point-on-s2-3 (a (m-trans p1)) (b (m-* (r3-m-inverse rot) rot))
                               (c p1) (x (id-rotation)))
                    (:instance associativity-of-m-*-2 (m1 (m-trans p1)) (m2 (id-rotation))
                               (m3 p1))
                    (:instance m-*point-id=point (p1 p1))
                    (:instance rotation*point-on-s2-6 (p1 p1))
                    (:instance array2p-alist2p-fname (l rot)))
              :in-theory (disable m-= m-* aref2 array2p associativity-of-m-*-2 m-*-m-inverse-m m-*point-id=point
                                  rotation*point-on-s2-3 rotation*point-on-s2-4 rotation*point-on-s2-5 rotation*point-on-s2-6)
              ))))

  (local
   (defthm rotation*point-on-s2-8
     (implies (and (point-in-r3 p1)
                   (r3-rotationp rot))
              (point-in-r3 (m-* rot p1)))))

  (local
   (defthmd rotation*point-on-s2-9-1
     (implies (and (point-in-r3 p1)
                   (r3-rotationp rot))
              (array2p :fake-name (m-* (m-trans (m-* rot p1)) rot p1)))
     :hints (("goal"
              :use ((:instance rotation*point-on-s2-4)
                    (:instance rotation*point-on-s2-7)
                    (:instance rotation*point-on-s2-6))
              :in-theory (disable rotation*point-on-s2-1 rotation*point-on-s2-2 rotation*point-on-s2-3 rotation*point-on-s2-4 rotation*point-on-s2-5 rotation*point-on-s2-6 rotation*point-on-s2-7 rotation*point-on-s2-8)
              ))))

  (local
   (defthmd rotation*point-on-s2-9
     (implies (and (point-in-r3 p1)
                   (r3-rotationp rot))
              (and (array2p :fake-name (m-* (m-trans (m-* rot p1)) rot p1))
                   (equal (cadr (dimensions :fake-name (m-* (m-trans (m-* rot p1)) rot p1)))
                          1)
                   (realp (aref2 :fake-name
                                 (m-* (m-trans (m-* rot p1)) rot p1)
                                 0 0))
                   (equal (car (dimensions :fake-name (m-* (m-trans (m-* rot p1)) rot p1)))
                          1)
                   (array2p :fake-name (m-* (m-trans p1) p1))
                   (realp (aref2 :fake-name (m-* (m-trans p1) p1)
                                 0 0))))
     :hints (("goal"
              :use ((:instance rotation*point-on-s2-9-1))
              :in-theory (disable rotation*point-on-s2-1 rotation*point-on-s2-2 rotation*point-on-s2-3 rotation*point-on-s2-4 rotation*point-on-s2-5 rotation*point-on-s2-6 rotation*point-on-s2-7 rotation*point-on-s2-8)
              ))))

  (defthm rotation*point-on-s2
    (implies (and (point-in-r3 p1)
                  (r3-rotationp rot)
                  (equal (m-* rot p1) p2))
             (equal (+ (* (aref2 :fake-name p1 0 0) (aref2 :fake-name p1 0 0))
                       (* (aref2 :fake-name p1 1 0) (aref2 :fake-name p1 1 0))
                       (* (aref2 :fake-name p1 2 0) (aref2 :fake-name p1 2 0)))
                    (+ (* (aref2 :fake-name p2 0 0) (aref2 :fake-name p2 0 0))
                       (* (aref2 :fake-name p2 1 0) (aref2 :fake-name p2 1 0))
                       (* (aref2 :fake-name p2 2 0) (aref2 :fake-name p2 2 0)))))
    :hints (("goal"
             :use ((:instance rotation*point-on-s2-7 (p1 p1) (rot rot))
                   (:instance m-*point1^t-point1 (x (m-* rot p1)))
                   (:instance rotation*point-on-s2-1 (p1 (m-* (m-trans (m-* rot p1)) (m-* rot p1)))
                              (p2 (m-* (m-trans p1) p1)))
                   (:instance rotation*point-on-s2-8)
                   (:instance rotation*point-on-s2-9)
                   (:instance m-*point1^t-point1 (x p1)))
             :in-theory nil
             )))
  )

(defun s2-def-p (point)
  (and (point-in-r3 point)
       (equal (+ (* (aref2 :fake-name point 0 0) (aref2 :fake-name point 0 0))
                 (* (aref2 :fake-name point 1 0) (aref2 :fake-name point 1 0))
                 (* (aref2 :fake-name point 2 0) (aref2 :fake-name point 2 0)))
              1)))

(defun-sk word-exists (point)
  (exists w
          (and (reducedwordp w)
               w
               (m-= (m-* (rotation w (acl2-sqrt 2)) point)
                    point))))

(defun d-p (point)
  (and (s2-def-p point)
       (word-exists point)))


(defun s2-d-p (point)
  (and (s2-def-p point)
       (not (d-p point))))

(defthmd s2-def-p-equiv
  (equal (s2-def-p p)
         (or (d-p p)
             (s2-d-p p))))

(defthm rot*p-on-s2
  (implies (and (s2-def-p p)
                (r3-rotationp rot))
           (s2-def-p (m-* rot p)))
  :hints (("goal"
           :use (:instance rotation*point-on-s2 (p1 p) (p2 (m-* rot p)))
           )))

(defthm d-p-implies
  (implies (d-p p)
           (let ((w (word-exists-witness p)))
             (and (s2-def-p p)
                  (reducedwordp w)
                  (not (equal w nil))
                  (m-= (m-* (rotation w (acl2-sqrt 2)) p)
                       p)))))

(defthmd d-p-implies-1
  (implies (and (s2-def-p point)
                (word-exists point))
           (d-p point)))

(defthm point-on-d=>rot*p-on-d
  (implies (and (reducedwordp w)
                (d-p (m-* (rotation w (acl2-sqrt 2)) p)))
           (let ((w1 (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) p))))
             (and (reducedwordp w1)
                  (not (equal w1 nil))
                  (m-= (m-* (rotation w1 (acl2-sqrt 2))
                            (m-* (rotation w (acl2-sqrt 2)) p))
                       (m-* (rotation w (acl2-sqrt 2)) p)))))
  :hints (("goal"
           :use ((:instance d-p-implies
                            (p (m-* (rotation w (acl2-sqrt 2)) p))))
           :in-theory nil
           )))

(defthm p-in-d-=>rot*p-in-d-lemma-1
  (implies (and (point-in-r3 p)
                (m-= (m-* m1 m2 p) (m-* m2 p)))
           (m-= (m-* m4 m1 m2 p) (m-* m4 m2 p))))

(defthmd p-in-d-=>rot*p-in-d-lemma-2
  (implies (and (reducedwordp w)
                (reducedwordp w1))
           (reducedwordp (compose (word-inverse w) (append w1 w))))
  :hints (("goal"
           :use ((:instance compose-assoc-lemma-export
                            (x (word-inverse w))
                            (y (append w1 w)))
                 (:instance reducedwordp=>weak-wordp (x w))
                 (:instance reducedwordp=>weak-wordp (x w1))
                 (:instance reducedwordp=>weak-wordp (x (word-inverse w)))
                 (:instance reducedwordp-word-inverse (x w))
                 (:instance closure-prop (x (word-inverse w)) (y (word-fix (append w1 w))))
                 (:instance closure-prop (x w1) (y w))
                 (:instance compose (x (word-inverse w)) (y (append w w1)))
                 (:instance compose (x w1) (y w))))))

(defthmd p-in-d-=>rot*p-in-d-lemma-3
  (implies (and (reducedwordp w)
                (reducedwordp w1))
           (m-= (rotation (compose (word-inverse w) (append w1 w)) (acl2-sqrt 2))
                (m-* (rotation (word-inverse w) (acl2-sqrt 2))
                     (rotation w1 (acl2-sqrt 2))
                     (rotation w (acl2-sqrt 2)))))
  :hints (("goal"
           :use ((:instance compose (x (word-inverse w)) (y (append w1 w)))
                 (:instance compose (x w1) (y w))
                 (:instance reducedwordp=>weak-wordp (x (word-inverse w)))
                 (:instance compose-assoc-lemma-export
                            (x (word-inverse w))
                            (y (append w1 w)))
                 (:instance rot-a*rot-b-= (a (word-inverse w)) (b (word-fix (append w1 w))) (x (acl2-sqrt 2)))
                 (:instance rot-a*rot-b-= (a w1) (b w) (x (acl2-sqrt 2)))
                 (:instance closure-prop (x w1) (y w))
                 (:instance closure-lemma (x w1) (y w))
                 (:instance compose (x w1) (y w))
                 (:instance reducedwordp-word-inverse (x w)))
           :do-not-induct t
           )))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-1
  (implies (m-= m1 (m-* m2 m3 m4))
           (m-= (m-* m5 m1) (m-* (m-* m5 m2) m3 m4))))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-2
  (implies (r3-matrixp m1)
           (m-= (m-* (id-rotation) m1) m1))
  :hints (("goal"
           :use ((:instance left-unity-of-m-1-for-m-* (m1 m1) (name :fake-name))
                 (:instance normalize-dimensions-name (name '$arg) (l m1))
                 (:instance array2p-alist2p-fname (l m1)))
           :in-theory (e/d (header dimensions default m-*) ())
           )))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-3
  (implies (m-= m1 (m-* m2 m3))
           (m-= (m-* m1 m4) (m-* m2 m3 m4))))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-4
  (implies (and (m-= (m-* m1 (id-rotation)) m5)
                (r3-matrixp m1)
                (r3-matrixp m3)
                (r3-matrixp m4)
                (m-= m2 (id-rotation))
                (m-= (m-* m1 (id-rotation)) (m-* m2 m3 m4)))
           (m-= m5 (m-* m3 m4)))
  :hints (("goal"
           :use ((:instance p-in-d-=>rot*p-in-d-lemma-4-2 (m1 m3))
                 (:instance p-in-d-=>rot*p-in-d-lemma-4-2 (m1 m4)))
           :in-theory (e/d (m-=) (m-* id-rotation))
           )))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-5
  (m-= (m-* m1 m2 m3) (m-* m1 (m-* m2 m3))))

(defthmd p-in-d-=>rot*p-in-d-lemma-4-6
  (implies (and (r3-matrixp m1)
                (m-= m2 (id-rotation))
                (m-= m2 (m-* m1 m2)))
           (m-= m1 (id-rotation)))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(encapsulate
  ()

  (local (in-theory nil))
  (local (include-book "supportive-theorems"))

  (defthmd p-in-d-=>rot*p-in-d-lemma-4
    (implies (and (reducedwordp w)
                  (reducedwordp w1)
                  (m-= (rotation (compose (word-inverse w) (append w1 w)) (acl2-sqrt 2))
                       (m-* (rotation (word-inverse w) (acl2-sqrt 2))
                            (rotation w1 (acl2-sqrt 2))
                            (rotation w (acl2-sqrt 2))))
                  (equal (compose (word-inverse w) (append w1 w)) nil))
             (m-= (rotation w1 (acl2-sqrt 2)) (id-rotation)))
    :hints (("goal"
             :use ((:instance p-in-d-=>rot*p-in-d-lemma-4-1
                              (m1 (id-rotation))
                              (m2 (rotation (word-inverse w) (acl2-sqrt 2)))
                              (m3 (rotation w1 (acl2-sqrt 2)))
                              (m4 (rotation w (acl2-sqrt 2)))
                              (m5 (rotation w (acl2-sqrt 2))))
                   (:instance rotation*point-on-s2-2 (m1 (rotation w (acl2-sqrt 2))))
                   (:instance rotation-is-r3-rotationp (x (acl2-sqrt 2)) (w w))
                   (:instance rotation-is-r3-rotationp (x (acl2-sqrt 2)) (w w1))
                   (:instance rot-a*rot-b-= (a w) (b (word-inverse w)) (x (acl2-sqrt 2)))
                   (:instance reduced-inverse (x w))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-3
                              (m1 (rotation w (acl2-sqrt 2)))
                              (m2 (rotation w1 (acl2-sqrt 2)))
                              (m3 (rotation w (acl2-sqrt 2)))
                              (m4 (rotation (word-inverse w) (acl2-sqrt 2))))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-2 (m1 (rotation w1 (acl2-sqrt 2))))
                   (:instance rotation*point-on-s2-2 (m1 (rotation w1
                                                                   (acl2-sqrt 2))))
                   (:instance rotation*point-on-s2-2 (m1 (rotation w (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (rotation w (acl2-sqrt 2))))
                   (:instance r3-rotationp (m (rotation w1 (acl2-sqrt 2))))
                   (:instance reducedwordp-word-inverse (x w))
                   (:instance rotation (w nil) (x (acl2-sqrt 2)))
                   (:instance r3-matrixp (m (rotation w (acl2-sqrt 2))))
                   (:instance r3-matrixp (m (rotation w1 (acl2-sqrt 2))))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-4
                              (m5 (rotation w (acl2-sqrt 2)))
                              (m1 (rotation w (acl2-sqrt 2)))
                              (m2 (m-* (rotation w (acl2-sqrt 2))
                                       (rotation (word-inverse w)
                                                 (acl2-sqrt 2))))
                              (m3 (rotation w1 (acl2-sqrt 2)))
                              (m4 (rotation w (acl2-sqrt 2))))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-5
                              (m1 (rotation w1 (acl2-sqrt 2)))
                              (m2 (rotation w (acl2-sqrt 2)))
                              (m3 (rotation (word-inverse w) (acl2-sqrt 2))))
                   (:instance p-in-d-=>rot*p-in-d-lemma-4-6
                              (m1 (rotation w1 (acl2-sqrt 2)))
                              (m2 (m-* (rotation w (acl2-sqrt 2)) (rotation (word-inverse w) (acl2-sqrt 2)))))
                   )))))

(defthmd p-in-d-=>rot*p-in-d-lemma-6
  (implies (and (reducedwordp w)
                w)
           (and (>= (len w) 0)
                (not (<= (len w) 0)))))

(defthmd p-in-d-=>rot*p-in-d-lemma-7
  (implies (m-= (m-* m1 m2 m3) (m-* m2 m3))
           (m-= (m-* (m-* m4 m1 m2) m3) (m-* (m-* m4 m2) m3))))

(defthmd p-in-d-=>rot*p-in-d-lemma-8
  (implies (and (m-= m1 m2)
                (m-= m3 m4)
                (m-= (m-* m4 m5) m6)
                (m-= (m-* m1 m5) (m-* m3 m5)))
           (m-= (m-* m2 m5) m6)))

(defthmd p-in-d-=>rot*p-in-d-lemma
  (implies (and (reducedwordp w)
                (s2-def-p point)
                (d-p (m-* (rotation w (acl2-sqrt 2)) point)))
           (d-p point))
  :hints (("goal"
           :use ((:instance word-exists-suff
                            (w (compose (word-inverse w)
                                        (append (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point)) w)))
                            (point point))
                 (:instance p-in-d-=>rot*p-in-d-lemma-2
                            (w w)
                            (w1 (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))))
                 (:instance p-in-d-=>rot*p-in-d-lemma-4 (w w)
                            (w1 (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))))
                 (:instance rotaion-not=id
                            (w (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point)))
                            (x (acl2-sqrt 2)))
                 (:instance point-on-d=>rot*p-on-d (w w) (p point))
                 (:instance p-in-d-=>rot*p-in-d-lemma-6
                            (w (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))))
                 (:instance p-in-d-=>rot*p-in-d-lemma-3
                            (w w)
                            (w1 (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))))
                 (:instance d-p-implies-1)
                 (:instance s2-def-p)
                 (:instance p-in-d-=>rot*p-in-d-lemma-7
                            (m1 (rotation (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))
                                          (acl2-sqrt 2)))
                            (m2 (rotation w (acl2-sqrt 2)))
                            (m3 point)
                            (m4 (rotation (word-inverse w) (acl2-sqrt 2))))
                 (:instance p-in-d-=>rot*p-in-d-lemma-8
                            (m1 (m-*
                                 (rotation (word-inverse w)
                                           (acl2-sqrt 2))
                                 (rotation (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))
                                           (acl2-sqrt 2))
                                 (rotation w (acl2-sqrt 2))))
                            (m2 (rotation
                                 (compose
                                  (word-inverse w)
                                  (append (word-exists-witness (m-* (rotation w (acl2-sqrt 2)) point))
                                          w))
                                 (acl2-sqrt 2)))
                            (m3 (m-* (rotation (word-inverse w)
                                               (acl2-sqrt 2))
                                     (rotation w (acl2-sqrt 2))))
                            (m4 (id-rotation))
                            (m6 point)
                            (m5 point))
                 (:instance rot-a*rot-b-= (a (word-inverse w)) (b w) (x (acl2-sqrt 2)))
                 (:instance reducedwordp-word-inverse (x w))
                 (:instance reducedwordp=>weak-wordp (x w))
                 (:instance reducedwordp=>weak-wordp (x (word-inverse w)))
                 (:instance inv-inv-x=x (x w))
                 (:instance reduced-inverse (x (word-inverse w)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 point))
                 )
           :in-theory nil
           )))

(defthmd s2-d-p=>p
  (implies (and (s2-d-p point)
                (reducedwordp w))
           (s2-d-p (m-* (rotation w (acl2-sqrt 2)) point)))
  :hints (("goal"
           :use ((:instance p-in-d-=>rot*p-in-d-lemma (w w) (point point))
                 (:instance s2-d-p (point point))
                 (:instance s2-d-p (point (m-* (rotation w (acl2-sqrt 2)) point)))
                 (:instance rot*p-on-s2 (p point) (rot (rotation w (acl2-sqrt 2))))
                 (:instance rotation-is-r3-rotationp (w w) (x (acl2-sqrt 2)))
                 (:instance s2-def-p-equiv (p point)))
           :in-theory nil
           )))

(defthmd s2-def-p-p=>p1
  (implies (and (s2-def-p p)
                (m-= p p1)
                (point-in-r3 p1))
           (s2-def-p p1))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd d-p-p=>d-p-p1-lemma
  (implies (and (m-= (m-* m1 m2) m2)
                (m-= m2 m3))
           (m-= (m-* m1 m3) m3)))

(defthmd d-p-p=>d-p-p1
  (implies (and (d-p p)
                (s2-def-p p1)
                (m-= p p1))
           (d-p p1))
  :hints (("goal"
           :use ((:instance d-p (point p1))
                 (:instance word-exists-suff (w (word-exists-witness p)) (point p1))
                 (:instance d-p-p=>d-p-p1-lemma (m1 (rotation (word-exists-witness p) (acl2-sqrt 2)))
                            (m2 p) (m3 p1)))

           :in-theory (disable acl2-sqrt)
           )))

(defthmd d-p-p=>d-p-p1-1
  (implies (and (d-p p)
                (s2-def-p p1)
                (m-= p1 p))
           (d-p p1))
  :hints (("goal"
           :use ((:instance d-p-p=>d-p-p1 (p p) (p1 p1)))
           )))

(defun-sk orbit-point-p-q (o-point point)
  (exists w
          (and (reducedwordp w)
               (m-= (m-* (rotation w (acl2-sqrt 2)) point) o-point))))

(defthmd orbit-point-p-q-equiv
  (implies (orbit-point-p-q o-p p)
           (and (reducedwordp (orbit-point-p-q-witness o-p p))
                (m-= (m-* (rotation (orbit-point-p-q-witness o-p p) (acl2-sqrt 2)) p)
                     o-p)))
  :hints (("goal"
           :in-theory (e/d () (reducedwordp))
           )))

(defchoose choice-set-s2-d-p (c-point) (p)
  (and (point-in-r3 c-point)
       (orbit-point-p-q c-point p))
  :strengthen t)

(defthmd choice-set-s2-d-p-rewrite
  (implies (and (point-in-r3 o-p)
                (orbit-point-p-q o-p p))
           (and (orbit-point-p-q (choice-set-s2-d-p p) p)
                (point-in-r3 (choice-set-s2-d-p p))))
  :hints (("goal"
           :use (:instance choice-set-s2-d-p (c-point o-p))
           )))

(defun-sk diff-s2-d-p-q-1 (cp1 p)
  (exists w
          (and (reducedwordp w)
               (m-= (m-* (rotation w (acl2-sqrt 2)) cp1) p))))

(defthmd diff-s2-d-p-q-1-equiv
  (implies (diff-s2-d-p-q-1 cp1 p)
           (and (reducedwordp (diff-s2-d-p-q-1-witness cp1 p))
                (m-= (m-* (rotation (diff-s2-d-p-q-1-witness cp1 p) (acl2-sqrt 2)) cp1) p)))
  :hints (("goal"
           :in-theory (e/d () (reducedwordp))
           )))

(defun-sk diff-s2-d-p-q (p)
  (exists p1
          (and (s2-d-p p1)
               (diff-s2-d-p-q-1 (choice-set-s2-d-p p1) p))))

(defthmd diff-s2-d-p-q-equiv
  (implies (diff-s2-d-p-q p)
           (and (s2-d-p (diff-s2-d-p-q-witness p))
                (diff-s2-d-p-q-1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p)))
  :hints (("goal"
           :in-theory (e/d () (reducedwordp))
           )))

(defun diff-s2-d-p (p)
  (and (point-in-r3 p)
       (diff-s2-d-p-q p)))

(defthmd s2-d-p-equiv-1-lemma1
  (implies (s2-d-p p)
           (orbit-point-p-q p p))
  :hints (("goal"
           :use ((:instance m-*point-id=point (p1 p))
                 (:instance orbit-point-p-q-suff (w nil) (point p) (o-point p)))
           )))

(defthmd s2-d-p-equiv-1-lemma2
  (implies (m-= (m-* m1 m2) m3)
           (m-= (m-* m4 m3)
                (m-* (m-* m4 m1) m2))))

(defthmd s2-d-p-equiv-1-lemma3
  (implies (and (m-= (m-* invx cp) (m-* (m-* invx x) p))
                (m-= (m-* invx x) id)
                (m-= (m-* id p) p))
           (m-= (m-* invx cp) p)))

(defthmd s2-d-p-equiv-1
  (implies (s2-d-p p)
           (diff-s2-d-p p))
  :hints (("goal"
           :use ((:instance diff-s2-d-p-q-suff (p1 p))
                 (:instance s2-d-p-equiv-1-lemma1 (p p))
                 (:instance orbit-point-p-q-equiv (o-p (choice-set-s2-d-p p)) (p p))
                 (:instance diff-s2-d-p-q-1-suff
                            (w (word-inverse (orbit-point-p-q-witness (choice-set-s2-d-p p) p)))
                            (cp1 (choice-set-s2-d-p p)) (p p))
                 (:instance choice-set-s2-d-p-rewrite (o-p p) (p p))
                 (:instance reducedwordp-word-inverse
                            (x (orbit-point-p-q-witness (choice-set-s2-d-p p) p)))
                 (:instance s2-d-p-equiv-1-lemma2
                            (m1 (rotation (orbit-point-p-q-witness (choice-set-s2-d-p p) p)
                                          (acl2-sqrt 2)))
                            (m2 p)
                            (m3 (choice-set-s2-d-p p))
                            (m4 (rotation (word-inverse (orbit-point-p-q-witness (choice-set-s2-d-p p) p))
                                          (acl2-sqrt 2))))
                 (:instance m-*rot-rot-inv=id
                            (p (word-inverse (orbit-point-p-q-witness (choice-set-s2-d-p p) p)))
                            (x (acl2-sqrt 2)))
                 (:instance inv-inv-x=x (x (orbit-point-p-q-witness (choice-set-s2-d-p p) p)))
                 (:instance reducedwordp=>weak-wordp
                            (x (orbit-point-p-q-witness (choice-set-s2-d-p p) p)))
                 (:instance m-*point-id=point (p1 p))
                 (:instance s2-d-p (point p))
                 (:instance s2-def-p (point p))
                 (:instance s2-d-p-equiv-1-lemma3
                            (invx (rotation (word-inverse (orbit-point-p-q-witness (choice-set-s2-d-p p) p))
                                            (acl2-sqrt 2)))
                            (x (rotation (orbit-point-p-q-witness (choice-set-s2-d-p p) p)
                                         (acl2-sqrt 2)))
                            (p p)
                            (id (id-rotation))
                            (cp (choice-set-s2-d-p p)))
                 (:instance diff-s2-d-p (p p))
                 )
           :in-theory nil
           )))

(defthmd s2-d-p-equiv-2-lemma1
  (implies (and (m-= (m-* x y) p)
                (m-= (m-* a b) y))
           (m-= (m-* (m-* x a) b) p)))

(defthmd s2-d-p-equiv-2-lemma2
  (implies (or (a-wordp w)
               (b-wordp w)
               (a-inv-wordp w)
               (b-inv-wordp w)
               (equal w nil))
           (reducedwordp w)))

(defthmd s2-d-p-equiv-2-lemma3
  (implies (and (m-= (m-* (m-* x y) diff) p)
                (m-= (m-* x y) a))
           (m-= (m-* a diff) p)))

(defthmd s2-d-p-equiv-2
  (implies (diff-s2-d-p p)
           (s2-d-p p))
  :hints (("goal"
           :use ((:instance choice-set-s2-d-p-rewrite
                            (p (diff-s2-d-p-q-witness p)) (o-p (diff-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (w nil)
                            (o-point (diff-s2-d-p-q-witness p))
                            (point (diff-s2-d-p-q-witness p)))
                 (:instance m-*point-id=point (p1 (diff-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-equiv (o-p (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p (diff-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-equiv
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance s2-d-p-equiv-2-lemma1
                            (x (rotation (diff-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p)
                                         (acl2-sqrt 2)))
                            (y (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p)
                            (b (diff-s2-d-p-q-witness p))
                            (a (rotation (orbit-point-p-q-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                                  (diff-s2-d-p-q-witness p))
                                         (acl2-sqrt 2))))
                 (:instance s2-d-p (point (diff-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-equiv (p p))
                 (:instance s2-def-p (point (diff-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance s2-d-p=>p
                            (point (diff-s2-d-p-q-witness p))
                            (w (compose (diff-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p)
                                        (orbit-point-p-q-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                                 (diff-s2-d-p-q-witness p)))))
                 (:instance s2-def-p-p=>p1
                            (p (m-*
                                (rotation
                                 (compose
                                  (diff-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                           p)
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                           (diff-s2-d-p-q-witness p)))
                                 (acl2-sqrt 2))
                                (diff-s2-d-p-q-witness p)))
                            (p1 p))
                 (:instance s2-def-p-equiv (p p))
                 (:instance s2-d-p (point
                                    (m-*
                                     (rotation
                                      (compose
                                       (diff-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                                p)
                                       (orbit-point-p-q-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                                (diff-s2-d-p-q-witness p)))
                                      (acl2-sqrt 2))
                                     (diff-s2-d-p-q-witness p))))

                 (:instance d-p-p=>d-p-p1-1 (p p)
                            (p1 (m-*
                                 (rotation
                                  (compose
                                   (diff-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                            p)
                                   (orbit-point-p-q-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                            (diff-s2-d-p-q-witness p)))
                                  (acl2-sqrt 2))
                                 (diff-s2-d-p-q-witness p))))
                 (:instance rot-a*rot-b-=
                            (a (diff-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (b (orbit-point-p-q-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                        (diff-s2-d-p-q-witness p)))
                            (x (acl2-sqrt 2)))
                 (:instance closure-prop
                            (x (diff-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (y (orbit-point-p-q-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                        (diff-s2-d-p-q-witness p))))
                 (:instance s2-d-p-equiv-2-lemma3
                            (x (rotation
                                (diff-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                         p)
                                (acl2-sqrt 2)))
                            (y (rotation
                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                         (diff-s2-d-p-q-witness p))
                                (acl2-sqrt 2)))
                            (a (rotation
                                (compose
                                 (diff-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                          p)
                                 (orbit-point-p-q-witness (choice-set-s2-d-p (diff-s2-d-p-q-witness p))
                                                          (diff-s2-d-p-q-witness p)))
                                (acl2-sqrt 2)))
                            (diff (diff-s2-d-p-q-witness p))
                            (p p))
                 )
           :in-theory nil
           )))

(defthmd s2-d-p-equiv
  (iff (s2-d-p p)
       (diff-s2-d-p p))
  :hints (("goal"
           :use ((:instance s2-d-p-equiv-2)
                 (:instance s2-d-p-equiv-1))
           )))

(defun-sk diff-n-s2-d-p-q-1 (cp1 p)
  (exists w
          (and (reducedwordp w)
               (equal w nil)
               (m-= (m-* (rotation w (acl2-sqrt 2)) cp1) p))))

(defthmd diff-n-s2-d-p-q-1-equiv
  (implies (diff-n-s2-d-p-q-1 cp1 p)
           (and (reducedwordp (diff-n-s2-d-p-q-1-witness cp1 p))
                (equal (diff-n-s2-d-p-q-1-witness cp1 p) nil)
                (m-= (m-* (rotation (diff-n-s2-d-p-q-1-witness cp1 p) (acl2-sqrt 2)) cp1) p))))

(defun-sk diff-n-s2-d-p-q (p)
  (exists p1
          (and (s2-d-p p1)
               (diff-n-s2-d-p-q-1 (choice-set-s2-d-p p1) p))))

(defthmd diff-n-s2-d-p-q-equiv
  (implies (diff-n-s2-d-p-q p)
           (and (s2-d-p (diff-n-s2-d-p-q-witness p))
                (diff-n-s2-d-p-q-1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)) p))))

(defun diff-n-s2-d-p (p)
  (and (point-in-r3 p)
       (diff-n-s2-d-p-q p)))

(defun-sk diff-a-s2-d-p-q-1 (cp1 p)
  (exists w
          (and (a-wordp w)
               (m-= (m-* (rotation w (acl2-sqrt 2)) cp1) p))))

(defthmd diff-a-s2-d-p-q-1-equiv
  (implies (diff-a-s2-d-p-q-1 cp1 p)
           (and (a-wordp (diff-a-s2-d-p-q-1-witness cp1 p))
                (m-= (m-* (rotation (diff-a-s2-d-p-q-1-witness cp1 p) (acl2-sqrt 2)) cp1) p)))
  :hints (("goal"
           :in-theory (e/d () (a-wordp))
           )))

(defun-sk diff-a-s2-d-p-q (p)
  (exists p1
          (and (s2-d-p p1)
               (diff-a-s2-d-p-q-1 (choice-set-s2-d-p p1) p))))

(defthmd diff-a-s2-d-p-q-equiv
  (implies (diff-a-s2-d-p-q p)
           (and (s2-d-p (diff-a-s2-d-p-q-witness p))
                (diff-a-s2-d-p-q-1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)) p)))
  :hints (("goal"
           :in-theory (e/d () (a-wordp))
           )))

(defun diff-a-s2-d-p (p)
  (and (point-in-r3 p)
       (diff-a-s2-d-p-q p)))

(defun-sk diff-b-s2-d-p-q-1 (cp1 p)
  (exists w
          (and (b-wordp w)
               (m-= (m-* (rotation w (acl2-sqrt 2)) cp1) p))))

(defthmd diff-b-s2-d-p-q-1-equiv
  (implies (diff-b-s2-d-p-q-1 cp1 p)
           (and (b-wordp (diff-b-s2-d-p-q-1-witness cp1 p))
                (m-= (m-* (rotation (diff-b-s2-d-p-q-1-witness cp1 p) (acl2-sqrt 2)) cp1) p)))
  :hints (("goal"
           :in-theory (e/d () (b-wordp))
           )))

(defun-sk diff-b-s2-d-p-q (p)
  (exists p1
          (and (s2-d-p p1)
               (diff-b-s2-d-p-q-1 (choice-set-s2-d-p p1) p))))

(defthmd diff-b-s2-d-p-q-equiv
  (implies (diff-b-s2-d-p-q p)
           (and (s2-d-p (diff-b-s2-d-p-q-witness p))
                (diff-b-s2-d-p-q-1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)) p)))
  :hints (("goal"
           :in-theory (e/d () (b-wordp))
           )))

(defun diff-b-s2-d-p (p)
  (and (point-in-r3 p)
       (diff-b-s2-d-p-q p)))

(defun-sk diff-a-inv-s2-d-p-q-1 (cp1 p)
  (exists w
          (and (a-inv-wordp w)
               (m-= (m-* (rotation w (acl2-sqrt 2)) cp1) p))))

(defthmd diff-a-inv-s2-d-p-q-1-equiv
  (implies (diff-a-inv-s2-d-p-q-1 cp1 p)
           (and (a-inv-wordp (diff-a-inv-s2-d-p-q-1-witness cp1 p))
                (m-= (m-* (rotation (diff-a-inv-s2-d-p-q-1-witness cp1 p) (acl2-sqrt 2)) cp1) p)))
  :hints (("goal"
           :in-theory (e/d () (a-inv-wordp))
           )))

(defun-sk diff-a-inv-s2-d-p-q (p)
  (exists p1
          (and (s2-d-p p1)
               (diff-a-inv-s2-d-p-q-1 (choice-set-s2-d-p p1) p))))

(defthmd diff-a-inv-s2-d-p-q-equiv
  (implies (diff-a-inv-s2-d-p-q p)
           (and (s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                (diff-a-inv-s2-d-p-q-1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)) p)))
  :hints (("goal"
           :in-theory (e/d () (a-inv-wordp))
           )))

(defun diff-a-inv-s2-d-p (p)
  (and (point-in-r3 p)
       (diff-a-inv-s2-d-p-q p)))

(defun-sk diff-b-inv-s2-d-p-q-1 (cp1 p)
  (exists w
          (and (b-inv-wordp w)
               (m-= (m-* (rotation w (acl2-sqrt 2)) cp1) p))))

(defthmd diff-b-inv-s2-d-p-q-1-equiv
  (implies (diff-b-inv-s2-d-p-q-1 cp1 p)
           (and (b-inv-wordp (diff-b-inv-s2-d-p-q-1-witness cp1 p))
                (m-= (m-* (rotation (diff-b-inv-s2-d-p-q-1-witness cp1 p) (acl2-sqrt 2)) cp1) p)))
  :hints (("goal"
           :in-theory (e/d () (b-inv-wordp))
           )))

(defun-sk diff-b-inv-s2-d-p-q (p)
  (exists p1
          (and (s2-d-p p1)
               (diff-b-inv-s2-d-p-q-1 (choice-set-s2-d-p p1) p))))

(defthmd diff-b-inv-s2-d-p-q-equiv
  (implies (diff-b-inv-s2-d-p-q p)
           (and (s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                (diff-b-inv-s2-d-p-q-1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)) p)))
  :hints (("goal"
           :in-theory (e/d () (b-inv-wordp))
           )))

(defun diff-b-inv-s2-d-p (p)
  (and (point-in-r3 p)
       (diff-b-inv-s2-d-p-q p)))

(defthmd diff-s2-d-p-=-1
  (implies (diff-s2-d-p p)
           (or (diff-n-s2-d-p p)
               (diff-a-s2-d-p p)
               (diff-a-inv-s2-d-p p)
               (diff-b-s2-d-p p)
               (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance diff-n-s2-d-p (p p))
                 (:instance diff-n-s2-d-p-q-suff (p1 (diff-s2-d-p-q-witness p)))
                 (:instance diff-n-s2-d-p-q-1-suff (w (diff-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-a-s2-d-p (p p))
                 (:instance diff-a-s2-d-p-q-suff (p1 (diff-s2-d-p-q-witness p)))
                 (:instance diff-a-s2-d-p-q-1-suff (w (diff-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-b-s2-d-p (p p))
                 (:instance diff-b-s2-d-p-q-suff (p1 (diff-s2-d-p-q-witness p)))
                 (:instance diff-b-s2-d-p-q-1-suff (w (diff-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-a-inv-s2-d-p (p p))
                 (:instance diff-a-inv-s2-d-p-q-suff (p1 (diff-s2-d-p-q-witness p)))
                 (:instance diff-a-inv-s2-d-p-q-1-suff (w (diff-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-b-inv-s2-d-p (p p))
                 (:instance diff-b-inv-s2-d-p-q-suff (p1 (diff-s2-d-p-q-witness p)))
                 (:instance diff-b-inv-s2-d-p-q-1-suff (w (diff-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-s2-d-p-q-equiv (p p))
                 (:instance diff-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance reducedwordp (x (diff-s2-d-p-q-1-witness
                                             (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p)))
                 (:instance diff-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p))) (p p))
                 (:instance diff-s2-d-p-q (p p))
                 )
           :in-theory nil
           )))

(defthmd diff-s2-d-p-=-2
  (implies (or (diff-n-s2-d-p p)
               (diff-a-s2-d-p p)
               (diff-a-inv-s2-d-p p)
               (diff-b-s2-d-p p)
               (diff-b-inv-s2-d-p p))
           (diff-s2-d-p p))
  :hints (("goal"
           :cases ((diff-n-s2-d-p p)
                   (diff-a-s2-d-p p)
                   (diff-b-s2-d-p p)
                   (diff-a-inv-s2-d-p p)
                   (diff-b-inv-s2-d-p p))
           :in-theory nil
           )
          ("subgoal 5"
           :use ((:instance diff-n-s2-d-p (p p))
                 (:instance diff-n-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))) (p p))
                 (:instance diff-n-s2-d-p-q (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-suff (p1 (diff-n-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-suff (w (diff-n-s2-d-p-q-1-witness
                                                     (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p p))
                 )
           )
          ("subgoal 4"
           :use ((:instance diff-a-s2-d-p (p p))
                 (:instance diff-a-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))) (p p))
                 (:instance diff-a-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))) (p p))
                 (:instance diff-a-s2-d-p-q (p p))
                 (:instance diff-a-s2-d-p-q-equiv (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-suff (p1 (diff-a-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-suff (w (diff-a-s2-d-p-q-1-witness
                                                     (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p p))
                 (:instance reducedwordp (x (diff-a-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)) p)))
                 )
           )
          ("subgoal 3"
           :use ((:instance diff-b-s2-d-p (p p))
                 (:instance diff-b-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))) (p p))
                 (:instance diff-a-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))) (p p))
                 (:instance diff-b-s2-d-p-q (p p))
                 (:instance diff-b-s2-d-p-q-equiv (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-suff (p1 (diff-b-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-suff (w (diff-b-s2-d-p-q-1-witness
                                                     (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p p))
                 (:instance reducedwordp (x (diff-b-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)) p)))
                 )
           )
          ("subgoal 2"
           :use ((:instance diff-a-inv-s2-d-p (p p))
                 (:instance diff-a-inv-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))) (p p))
                 (:instance diff-a-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))) (p p))
                 (:instance diff-a-inv-s2-d-p-q (p p))
                 (:instance diff-a-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-suff (p1 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-suff (w (diff-a-inv-s2-d-p-q-1-witness
                                                     (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance reducedwordp (x (diff-a-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)) p)))
                 )
           )
          ("subgoal 1"
           :use ((:instance diff-b-inv-s2-d-p (p p))
                 (:instance diff-b-inv-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))) (p p))
                 (:instance diff-b-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))) (p p))
                 (:instance diff-b-inv-s2-d-p-q (p p))
                 (:instance diff-b-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-suff (p1 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-suff (w (diff-b-inv-s2-d-p-q-1-witness
                                                     (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance reducedwordp (x (diff-b-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)) p)))
                 )
           )
          ))

(defthmd diff-s2-d-p-equivalence-1
  (iff (diff-s2-d-p p)
       (or (diff-n-s2-d-p p)
           (diff-a-s2-d-p p)
           (diff-a-inv-s2-d-p p)
           (diff-b-s2-d-p p)
           (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance diff-s2-d-p-=-1)
                 (:instance diff-s2-d-p-=-2))
           )))

(defun-sk diff-a-inv-wa-s2-d-p-q-1 (cp1 p)
  (exists w
          (and (a-inv*w-a-p w)
               (m-= (m-* (rotation w (acl2-sqrt 2)) cp1) p))))

(defthmd diff-a-inv-wa-s2-d-p-q-1-equiv
  (implies (diff-a-inv-wa-s2-d-p-q-1 cp1 p)
           (and (a-inv*w-a-p (diff-a-inv-wa-s2-d-p-q-1-witness cp1 p))
                (m-= (m-* (rotation (diff-a-inv-wa-s2-d-p-q-1-witness cp1 p) (acl2-sqrt 2)) cp1) p)))
  :hints (("goal"
           :in-theory (e/d () (a-inv*w-a-p))
           )))

(defun-sk diff-a-inv-wa-s2-d-p-q (p)
  (exists p1
          (and (s2-d-p p1)
               (diff-a-inv-wa-s2-d-p-q-1 (choice-set-s2-d-p p1) p))))

(defthmd diff-a-inv-wa-s2-d-p-q-equiv
  (implies (diff-a-inv-wa-s2-d-p-q p)
           (and (s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                (diff-a-inv-wa-s2-d-p-q-1 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)) p)))
  :hints (("goal"
           :in-theory (e/d () (a-inv*w-a-p))
           )))

(defun diff-a-inv-wa-s2-d-p (p)
  (and (point-in-r3 p)
       (diff-a-inv-wa-s2-d-p-q p)))

(defthmd diff-s2-d-p-=-3
  (implies (diff-s2-d-p p)
           (or (diff-a-inv-wa-s2-d-p p)
               (diff-a-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance diff-a-inv-wa-s2-d-p (p p))
                 (:instance diff-a-inv-wa-s2-d-p-q-suff (p1 (diff-s2-d-p-q-witness p)))
                 (:instance diff-a-inv-wa-s2-d-p-q-1-suff (w (diff-s2-d-p-q-1-witness
                                                              (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-a-inv-s2-d-p (p p))
                 (:instance diff-a-inv-s2-d-p-q-suff (p1 (diff-s2-d-p-q-witness p)))
                 (:instance diff-a-inv-s2-d-p-q-1-suff (w (diff-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-s2-d-p-q-equiv (p p))
                 (:instance diff-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance reducedword-equiv-4 (w (diff-s2-d-p-q-1-witness
                                                    (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p)))
                 (:instance diff-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p))) (p p))
                 (:instance diff-s2-d-p-q (p p))
                 )
           :in-theory nil
           )))

(defthmd diff-s2-d-p-=-4-1
  (implies (a-inv*w-a-p w)
           (reducedwordp w))
  :hints (("goal"
           :use ((:instance a-inv*w-a-p-equiv (w w)))
           :in-theory (disable a-inv*w-a-p)
           )))

(defthmd diff-s2-d-p-=-4
  (implies (or (diff-a-inv-wa-s2-d-p p)
               (diff-a-inv-s2-d-p p))
           (diff-s2-d-p p))
  :hints (("goal"
           :cases ((diff-a-inv-wa-s2-d-p p)
                   (diff-a-inv-s2-d-p p))
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance diff-a-inv-wa-s2-d-p (p p))
                 (:instance diff-a-inv-wa-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))) (p p))
                 (:instance diff-a-inv-wa-s2-d-p-q (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-suff (p1 (diff-a-inv-wa-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-suff (w (diff-a-inv-wa-s2-d-p-q-1-witness
                                                     (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (p p))
                 (:instance a-inv*w-a-p-equiv (w (diff-a-inv-wa-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                  p)))
                 (:instance diff-s2-d-p-=-4-1 (w (diff-a-inv-wa-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                  p)))
                 )
           )
          ("subgoal 1"
           :use ((:instance diff-a-inv-s2-d-p (p p))
                 (:instance diff-a-inv-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))) (p p))
                 (:instance diff-a-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))) (p p))
                 (:instance diff-a-inv-s2-d-p-q (p p))
                 (:instance diff-a-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-suff (p1 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-suff (w (diff-a-inv-s2-d-p-q-1-witness
                                                     (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance reducedwordp (x (diff-a-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)) p)))
                 )
           )))

(defthmd diff-s2-d-p-equivalence-2
  (iff (diff-s2-d-p p)
       (or (diff-a-inv-wa-s2-d-p p)
           (diff-a-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance diff-s2-d-p-=-3)
                 (:instance diff-s2-d-p-=-4))
           )))

(defun-sk diff-b-inv-wb-s2-d-p-q-1 (cp1 p)
  (exists w
          (and (b-inv*w-b-p w)
               (m-= (m-* (rotation w (acl2-sqrt 2)) cp1) p))))

(defthmd diff-b-inv-wb-s2-d-p-q-1-equiv
  (implies (diff-b-inv-wb-s2-d-p-q-1 cp1 p)
           (and (b-inv*w-b-p (diff-b-inv-wb-s2-d-p-q-1-witness cp1 p))
                (m-= (m-* (rotation (diff-b-inv-wb-s2-d-p-q-1-witness cp1 p) (acl2-sqrt 2)) cp1) p)))
  :hints (("goal"
           :in-theory (e/d () (b-inv*w-b-p))
           )))

(defun-sk diff-b-inv-wb-s2-d-p-q (p)
  (exists p1
          (and (s2-d-p p1)
               (diff-b-inv-wb-s2-d-p-q-1 (choice-set-s2-d-p p1) p))))

(defthmd diff-b-inv-wb-s2-d-p-q-equiv
  (implies (diff-b-inv-wb-s2-d-p-q p)
           (and (s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                (diff-b-inv-wb-s2-d-p-q-1 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)) p)))
  :hints (("goal"
           :in-theory (e/d () (b-inv*w-b-p))
           )))

(defun diff-b-inv-wb-s2-d-p (p)
  (and (point-in-r3 p)
       (diff-b-inv-wb-s2-d-p-q p)))

(defthmd diff-s2-d-p-=-5
  (implies (diff-s2-d-p p)
           (or (diff-b-inv-wb-s2-d-p p)
               (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance diff-b-inv-wb-s2-d-p (p p))
                 (:instance diff-b-inv-wb-s2-d-p-q-suff (p1 (diff-s2-d-p-q-witness p)))
                 (:instance diff-b-inv-wb-s2-d-p-q-1-suff (w (diff-s2-d-p-q-1-witness
                                                              (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-b-inv-s2-d-p (p p))
                 (:instance diff-b-inv-s2-d-p-q-suff (p1 (diff-s2-d-p-q-witness p)))
                 (:instance diff-b-inv-s2-d-p-q-1-suff (w (diff-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-s2-d-p-q-equiv (p p))
                 (:instance diff-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance reducedword-equiv-2 (w (diff-s2-d-p-q-1-witness
                                                    (choice-set-s2-d-p (diff-s2-d-p-q-witness p)) p)))
                 (:instance diff-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-s2-d-p-q-witness p))) (p p))
                 (:instance diff-s2-d-p-q (p p))
                 )
           :in-theory nil
           )))

(defthmd diff-s2-d-p-=-6-1
  (implies (b-inv*w-b-p w)
           (reducedwordp w))
  :hints (("goal"
           :use ((:instance b-inv*w-b-p-equiv (w w)))
           :in-theory (disable b-inv*w-b-p)
           )))

(defthmd diff-s2-d-p-=-6
  (implies (or (diff-b-inv-wb-s2-d-p p)
               (diff-b-inv-s2-d-p p))
           (diff-s2-d-p p))
  :hints (("goal"
           :cases ((diff-b-inv-wb-s2-d-p p)
                   (diff-b-inv-s2-d-p p))
           :in-theory nil
           )
          ("subgoal 2"
           :use ((:instance diff-b-inv-wb-s2-d-p (p p))
                 (:instance diff-b-inv-wb-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))) (p p))
                 (:instance diff-b-inv-wb-s2-d-p-q (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-suff (p1 (diff-b-inv-wb-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-suff (w (diff-b-inv-wb-s2-d-p-q-1-witness
                                                     (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (p p))
                 (:instance b-inv*w-b-p-equiv (w (diff-b-inv-wb-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                  p)))
                 (:instance diff-s2-d-p-=-6-1 (w (diff-b-inv-wb-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                  p)))
                 )
           )
          ("subgoal 1"
           :use ((:instance diff-b-inv-s2-d-p (p p))
                 (:instance diff-b-inv-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))) (p p))
                 (:instance diff-b-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))) (p p))
                 (:instance diff-b-inv-s2-d-p-q (p p))
                 (:instance diff-b-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-s2-d-p (p p))
                 (:instance diff-s2-d-p-q-suff (p1 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance diff-s2-d-p-q-1-suff (w (diff-b-inv-s2-d-p-q-1-witness
                                                     (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)) p))
                            (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance reducedwordp (x (diff-b-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)) p)))
                 )
           )))

(defthmd diff-s2-d-p-equivalence-3
  (iff (diff-s2-d-p p)
       (or (diff-b-inv-wb-s2-d-p p)
           (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance diff-s2-d-p-=-5)
                 (:instance diff-s2-d-p-=-6))
           )))

(defun-sk a-inv-diff-a-s2-d-p-1 (p)
  (exists p1
          (and (diff-a-s2-d-p p1)
               (m-= (m-* (rotation (list (wa-inv)) (acl2-sqrt 2)) p1) p))))

(defthmd a-inv-diff-a-s2-d-p-1-equiv
  (implies (a-inv-diff-a-s2-d-p-1 p)
           (and (diff-a-s2-d-p (a-inv-diff-a-s2-d-p-1-witness p))
                (m-= (m-* (rotation (list (wa-inv)) (acl2-sqrt 2)) (a-inv-diff-a-s2-d-p-1-witness p)) p)))
  :hints (("goal"
           :in-theory (disable rotation reducedwordp)
           )))

(defun-sk b-inv-diff-b-s2-d-p-1 (p)
  (exists p1
          (and (diff-b-s2-d-p p1)
               (m-= (m-* (rotation (list (wb-inv)) (acl2-sqrt 2)) p1) p))))

(defthmd b-inv-diff-b-s2-d-p-1-equiv
  (implies (b-inv-diff-b-s2-d-p-1 p)
           (and (diff-b-s2-d-p (b-inv-diff-b-s2-d-p-1-witness p))
                (m-= (m-* (rotation (list (wb-inv)) (acl2-sqrt 2)) (b-inv-diff-b-s2-d-p-1-witness p)) p)))
  :hints (("goal"
           :in-theory (disable rotation reducedwordp)
           )))

(defun a-inv-diff-a-s2-d-p (p)
  (and (point-in-r3 p)
       (a-inv-diff-a-s2-d-p-1 p)))

(defun b-inv-diff-b-s2-d-p (p)
  (and (point-in-r3 p)
       (b-inv-diff-b-s2-d-p-1 p)))

(defthmd s2-d-p-orbit
  (implies (s2-d-p p)
           (and (orbit-point-p-q p p)
                (point-in-r3 (choice-set-s2-d-p p))
                (reducedwordp (orbit-point-p-q-witness (choice-set-s2-d-p p) p))
                (m-= (m-* (rotation (orbit-point-p-q-witness (choice-set-s2-d-p p) p) (acl2-sqrt 2)) p)
                     (choice-set-s2-d-p p))
                (s2-d-p (choice-set-s2-d-p p))))
  :hints (("goal"
           :use ((:instance orbit-point-p-q-suff (w nil) (point p) (o-point p))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance choice-set-s2-d-p-rewrite (o-p p) (p p))
                 (:instance s2-d-p (point p))
                 (:instance s2-def-p (point p))
                 (:instance orbit-point-p-q-equiv (o-p (choice-set-s2-d-p p)) (p p))
                 (:instance s2-d-p=>p (point p)
                            (w (orbit-point-p-q-witness (choice-set-s2-d-p p) p)))
                 (:instance s2-d-p
                            (point (m-* (rotation (orbit-point-p-q-witness (choice-set-s2-d-p p) p) (acl2-sqrt 2)) p)))
                 (:instance s2-def-p-p=>p1
                            (p (m-* (rotation (orbit-point-p-q-witness (choice-set-s2-d-p p) p) (acl2-sqrt 2)) p))
                            (p1 (choice-set-s2-d-p p)))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p p))
                            (p1 (m-* (rotation (orbit-point-p-q-witness (choice-set-s2-d-p p) p) (acl2-sqrt 2)) p)))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p p))))
           :in-theory nil
           )))

(defthmd diff-a-inv-wa-s2-d-p-equiv-1-1
  (implies (and (m-= (m-* a b) p)
                (m-= (m-* x y) a))
           (m-= (m-* x y b) p)))

(defthmd diff-a-inv-wa-s2-d-p-equiv-1-2
  (reducedwordp (list (wa-inv))))

(defthmd diff-a-inv-wa-s2-d-p-equiv-1
  (implies (diff-a-inv-wa-s2-d-p p)
           (a-inv-diff-a-s2-d-p p))
  :hints (("goal"
           :use ((:instance diff-a-inv-wa-s2-d-p (p p))
                 (:instance diff-a-inv-wa-s2-d-p-q-equiv (p p))
                 (:instance diff-a-inv-wa-s2-d-p-q-1-equiv
                            (cp1 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (p p))
                 (:instance a-inv*w-a-p-equiv-1 (w (diff-a-inv-wa-s2-d-p-q-1-witness
                                                    (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                    p)))
                 (:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1-suff (p p)
                            (p1 (m-* (rotation (a-inv*w-a-p-witness
                                                (diff-a-inv-wa-s2-d-p-q-1-witness
                                                 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                 p))
                                               (acl2-sqrt 2))
                                     (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                                ))
                 (:instance diff-a-s2-d-p
                            (p (m-*
                                (rotation
                                 (a-inv*w-a-p-witness
                                  (diff-a-inv-wa-s2-d-p-q-1-witness
                                   (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                   p))
                                 (acl2-sqrt 2))
                                (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))))
                 (:instance s2-d-p-orbit (p (diff-a-inv-wa-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (point (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (w (a-inv*w-a-p-witness
                                (diff-a-inv-wa-s2-d-p-q-1-witness
                                 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                 p))))
                 (:instance s2-d-p-equiv-2-lemma2 (w (a-inv*w-a-p-witness
                                                      (diff-a-inv-wa-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                       p))))
                 (:instance s2-d-p
                            (point (m-* (rotation
                                         (a-inv*w-a-p-witness
                                          (diff-a-inv-wa-s2-d-p-q-1-witness
                                           (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                           p))
                                         (acl2-sqrt 2))
                                        (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))))
                 (:instance s2-def-p
                            (point (m-* (rotation
                                         (a-inv*w-a-p-witness
                                          (diff-a-inv-wa-s2-d-p-q-1-witness
                                           (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                           p))
                                         (acl2-sqrt 2))
                                        (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))))
                 (:instance diff-a-s2-d-p-q-suff
                            (p1 (diff-a-inv-wa-s2-d-p-q-witness p))
                            (p (m-* (rotation (a-inv*w-a-p-witness
                                               (diff-a-inv-wa-s2-d-p-q-1-witness
                                                (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                p))
                                              (acl2-sqrt 2))
                                    (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))))
                 (:instance diff-a-s2-d-p-q-1-suff
                            (cp1 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (p (m-*
                                (rotation
                                 (a-inv*w-a-p-witness
                                  (diff-a-inv-wa-s2-d-p-q-1-witness
                                   (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                   p))
                                 (acl2-sqrt 2))
                                (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))))
                            (w (a-inv*w-a-p-witness
                                (diff-a-inv-wa-s2-d-p-q-1-witness
                                 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                 p))))
                 (:instance diff-a-inv-wa-s2-d-p-equiv-1-1
                            (a (rotation (diff-a-inv-wa-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                          p)
                                         (acl2-sqrt 2)))
                            (b (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (p p)
                            (x (rotation (list (wa-inv)) (acl2-sqrt 2)))
                            (y (rotation
                                (a-inv*w-a-p-witness
                                 (diff-a-inv-wa-s2-d-p-q-1-witness
                                  (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                  p))
                                (acl2-sqrt 2))))
                 (:instance rot-a*rot-b-= (a (list (wa-inv)))
                            (x (acl2-sqrt 2))
                            (b (a-inv*w-a-p-witness
                                (diff-a-inv-wa-s2-d-p-q-1-witness
                                 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                 p))))
                 (:instance diff-a-inv-wa-s2-d-p-equiv-1-2)
                 )
           :in-theory nil
           )))

(defthmd diff-a-inv-wa-s2-d-p-equiv-2-1
  (reducedwordp (list (wa-inv))))

(defthmd diff-a-inv-wa-s2-d-p-equiv-2-2-1
  (implies (and (m-= (m-* x y) p)
                (m-= (m-* d c) y)
                (m-= (m-* x d) co))
           (m-= (m-* co c) p)))

(defthmd diff-a-inv-wa-s2-d-p-equiv-2-2
  (implies (and (reducedwordp wa-inv)
                (a-wordp diff)
                (m-= (m-* (rotation wa-inv (acl2-sqrt 2)) a-inv-wit) p)
                (m-= (m-* (rotation diff (acl2-sqrt 2)) cp) a-inv-wit))
           (m-= (m-* (rotation (compose wa-inv diff) (acl2-sqrt 2)) cp) p))
  :hints (("goal"
           :use ((:instance rot-a*rot-b-= (a wa-inv) (b diff) (x (acl2-sqrt 2)))
                 (:instance s2-d-p-equiv-2-lemma2 (w diff))
                 (:instance diff-a-inv-wa-s2-d-p-equiv-2-2-1 (x (rotation wa-inv (acl2-sqrt 2)))
                            (p p) (y a-inv-wit)
                            (co (rotation (compose wa-inv diff) (acl2-sqrt 2)))
                            (d (rotation diff (acl2-sqrt 2)))
                            (c cp)))
           :in-theory nil
           :do-not-induct t
           )))

(defthmd diff-a-inv-wa-s2-d-p-equiv-2
  (implies (a-inv-diff-a-s2-d-p p)
           (diff-a-inv-wa-s2-d-p p))
  :hints (("goal"
           :use ((:instance a-inv-diff-a-s2-d-p (p p))
                 (:instance a-inv-diff-a-s2-d-p-1-equiv (p p))
                 (:instance diff-a-s2-d-p (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance diff-a-s2-d-p-q-equiv (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance diff-a-s2-d-p-q-1-equiv
                            (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness (a-inv-diff-a-s2-d-p-1-witness p))))
                            (p (a-inv-diff-a-s2-d-p-1-witness p)))
                 (:instance diff-a-inv-wa-s2-d-p (p p))
                 (:instance diff-a-inv-wa-s2-d-p-q-suff
                            (p1 (diff-a-s2-d-p-q-witness (a-inv-diff-a-s2-d-p-1-witness p)))
                            (p p))
                 (:instance diff-a-inv-wa-s2-d-p-q-1-suff
                            (w (compose (list (wa-inv)) (diff-a-s2-d-p-q-1-witness
                                                         (choice-set-s2-d-p
                                                          (diff-a-s2-d-p-q-witness (a-inv-diff-a-s2-d-p-1-witness p)))
                                                         (a-inv-diff-a-s2-d-p-1-witness p))))
                            (cp1 (choice-set-s2-d-p
                                  (diff-a-s2-d-p-q-witness (a-inv-diff-a-s2-d-p-1-witness p))))
                            (p p))
                 (:instance a-inv*w-a-p-suff
                            (word-a (diff-a-s2-d-p-q-1-witness
                                     (choice-set-s2-d-p
                                      (diff-a-s2-d-p-q-witness (a-inv-diff-a-s2-d-p-1-witness p)))
                                     (a-inv-diff-a-s2-d-p-1-witness p)))
                            (w (compose (list (wa-inv)) (diff-a-s2-d-p-q-1-witness
                                                         (choice-set-s2-d-p
                                                          (diff-a-s2-d-p-q-witness (a-inv-diff-a-s2-d-p-1-witness p)))
                                                         (a-inv-diff-a-s2-d-p-1-witness p)))))
                 (:instance diff-a-inv-wa-s2-d-p-equiv-2-1)
                 (:instance diff-a-inv-wa-s2-d-p-equiv-2-2
                            (wa-inv (list (wa-inv)))
                            (diff (diff-a-s2-d-p-q-1-witness
                                   (choice-set-s2-d-p
                                    (diff-a-s2-d-p-q-witness (a-inv-diff-a-s2-d-p-1-witness p)))
                                   (a-inv-diff-a-s2-d-p-1-witness p)))
                            (a-inv-wit (a-inv-diff-a-s2-d-p-1-witness p))
                            (cp (choice-set-s2-d-p
                                 (diff-a-s2-d-p-q-witness (a-inv-diff-a-s2-d-p-1-witness p))))
                            (p p))
                 )
           :in-theory nil
           )))

(defthmd diff-a-inv-wa-s2-d-p-equiv
  (iff (diff-a-inv-wa-s2-d-p p)
       (a-inv-diff-a-s2-d-p p))
  :hints (("goal"
           :use ((:instance diff-a-inv-wa-s2-d-p-equiv-1)
                 (:instance diff-a-inv-wa-s2-d-p-equiv-2))
           )))

(defthmd diff-b-inv-wb-s2-d-p-equiv-1-2
  (reducedwordp (list (wb-inv))))

(defthmd diff-b-inv-wb-s2-d-p-equiv-1
  (implies (diff-b-inv-wb-s2-d-p p)
           (b-inv-diff-b-s2-d-p p))
  :hints (("goal"
           :use ((:instance diff-b-inv-wb-s2-d-p (p p))
                 (:instance diff-b-inv-wb-s2-d-p-q-equiv (p p))
                 (:instance diff-b-inv-wb-s2-d-p-q-1-equiv
                            (cp1 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (p p))
                 (:instance b-inv*w-b-p-equiv-1 (w (diff-b-inv-wb-s2-d-p-q-1-witness
                                                    (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                    p)))
                 (:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1-suff (p p)
                            (p1 (m-* (rotation (b-inv*w-b-p-witness
                                                (diff-b-inv-wb-s2-d-p-q-1-witness
                                                 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                 p))
                                               (acl2-sqrt 2))
                                     (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                                ))
                 (:instance diff-b-s2-d-p
                            (p (m-*
                                (rotation
                                 (b-inv*w-b-p-witness
                                  (diff-b-inv-wb-s2-d-p-q-1-witness
                                   (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                   p))
                                 (acl2-sqrt 2))
                                (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))))
                 (:instance s2-d-p-orbit (p (diff-b-inv-wb-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (point (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (w (b-inv*w-b-p-witness
                                (diff-b-inv-wb-s2-d-p-q-1-witness
                                 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                 p))))
                 (:instance s2-d-p-equiv-2-lemma2 (w (b-inv*w-b-p-witness
                                                      (diff-b-inv-wb-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                       p))))
                 (:instance s2-d-p
                            (point (m-* (rotation
                                         (b-inv*w-b-p-witness
                                          (diff-b-inv-wb-s2-d-p-q-1-witness
                                           (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                           p))
                                         (acl2-sqrt 2))
                                        (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))))
                 (:instance s2-def-p
                            (point (m-* (rotation
                                         (b-inv*w-b-p-witness
                                          (diff-b-inv-wb-s2-d-p-q-1-witness
                                           (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                           p))
                                         (acl2-sqrt 2))
                                        (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))))
                 (:instance diff-b-s2-d-p-q-suff
                            (p1 (diff-b-inv-wb-s2-d-p-q-witness p))
                            (p (m-* (rotation (b-inv*w-b-p-witness
                                               (diff-b-inv-wb-s2-d-p-q-1-witness
                                                (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                p))
                                              (acl2-sqrt 2))
                                    (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))))
                 (:instance diff-b-s2-d-p-q-1-suff
                            (cp1 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (p (m-*
                                (rotation
                                 (b-inv*w-b-p-witness
                                  (diff-b-inv-wb-s2-d-p-q-1-witness
                                   (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                   p))
                                 (acl2-sqrt 2))
                                (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))))
                            (w (b-inv*w-b-p-witness
                                (diff-b-inv-wb-s2-d-p-q-1-witness
                                 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                 p))))
                 (:instance diff-a-inv-wa-s2-d-p-equiv-1-1
                            (a (rotation (diff-b-inv-wb-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                          p)
                                         (acl2-sqrt 2)))
                            (b (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (p p)
                            (x (rotation (list (wb-inv)) (acl2-sqrt 2)))
                            (y (rotation
                                (b-inv*w-b-p-witness
                                 (diff-b-inv-wb-s2-d-p-q-1-witness
                                  (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                  p))
                                (acl2-sqrt 2))))
                 (:instance rot-a*rot-b-= (a (list (wb-inv)))
                            (x (acl2-sqrt 2))
                            (b (b-inv*w-b-p-witness
                                (diff-b-inv-wb-s2-d-p-q-1-witness
                                 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                 p))))
                 (:instance diff-b-inv-wb-s2-d-p-equiv-1-2)
                 )
           :in-theory nil
           )))

(defthmd diff-b-inv-wb-s2-d-p-equiv-2-1
  (reducedwordp (list (wb-inv))))

(defthmd diff-b-inv-wb-s2-d-p-equiv-2-2-1
  (implies (and (m-= (m-* x y) p)
                (m-= (m-* d c) y)
                (m-= (m-* x d) co))
           (m-= (m-* co c) p)))

(defthmd diff-b-inv-wb-s2-d-p-equiv-2-2
  (implies (and (reducedwordp wb-inv)
                (b-wordp diff)
                (m-= (m-* (rotation wb-inv (acl2-sqrt 2)) b-inv-wit) p)
                (m-= (m-* (rotation diff (acl2-sqrt 2)) cp) b-inv-wit))
           (m-= (m-* (rotation (compose wb-inv diff) (acl2-sqrt 2)) cp) p))
  :hints (("goal"
           :use ((:instance rot-a*rot-b-= (a wb-inv) (b diff) (x (acl2-sqrt 2)))
                 (:instance s2-d-p-equiv-2-lemma2 (w diff))
                 (:instance diff-b-inv-wb-s2-d-p-equiv-2-2-1 (x (rotation wb-inv (acl2-sqrt 2)))
                            (p p) (y b-inv-wit)
                            (co (rotation (compose wb-inv diff) (acl2-sqrt 2)))
                            (d (rotation diff (acl2-sqrt 2)))
                            (c cp)))
           :in-theory nil
           :do-not-induct t
           )))

(defthmd diff-b-inv-wb-s2-d-p-equiv-2
  (implies (b-inv-diff-b-s2-d-p p)
           (diff-b-inv-wb-s2-d-p p))
  :hints (("goal"
           :use ((:instance b-inv-diff-b-s2-d-p (p p))
                 (:instance b-inv-diff-b-s2-d-p-1-equiv (p p))
                 (:instance diff-b-s2-d-p (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance diff-b-s2-d-p-q-equiv (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance diff-b-s2-d-p-q-1-equiv
                            (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness (b-inv-diff-b-s2-d-p-1-witness p))))
                            (p (b-inv-diff-b-s2-d-p-1-witness p)))
                 (:instance diff-b-inv-wb-s2-d-p (p p))
                 (:instance diff-b-inv-wb-s2-d-p-q-suff
                            (p1 (diff-b-s2-d-p-q-witness (b-inv-diff-b-s2-d-p-1-witness p)))
                            (p p))
                 (:instance diff-b-inv-wb-s2-d-p-q-1-suff
                            (w (compose (list (wb-inv)) (diff-b-s2-d-p-q-1-witness
                                                         (choice-set-s2-d-p
                                                          (diff-b-s2-d-p-q-witness (b-inv-diff-b-s2-d-p-1-witness p)))
                                                         (b-inv-diff-b-s2-d-p-1-witness p))))
                            (cp1 (choice-set-s2-d-p
                                  (diff-b-s2-d-p-q-witness (b-inv-diff-b-s2-d-p-1-witness p))))
                            (p p))
                 (:instance b-inv*w-b-p-suff
                            (word-b (diff-b-s2-d-p-q-1-witness
                                     (choice-set-s2-d-p
                                      (diff-b-s2-d-p-q-witness (b-inv-diff-b-s2-d-p-1-witness p)))
                                     (b-inv-diff-b-s2-d-p-1-witness p)))
                            (w (compose (list (wb-inv)) (diff-b-s2-d-p-q-1-witness
                                                         (choice-set-s2-d-p
                                                          (diff-b-s2-d-p-q-witness (b-inv-diff-b-s2-d-p-1-witness p)))
                                                         (b-inv-diff-b-s2-d-p-1-witness p)))))
                 (:instance diff-b-inv-wb-s2-d-p-equiv-2-1)
                 (:instance diff-b-inv-wb-s2-d-p-equiv-2-2
                            (wb-inv (list (wb-inv)))
                            (diff (diff-b-s2-d-p-q-1-witness
                                   (choice-set-s2-d-p
                                    (diff-b-s2-d-p-q-witness (b-inv-diff-b-s2-d-p-1-witness p)))
                                   (b-inv-diff-b-s2-d-p-1-witness p)))
                            (b-inv-wit (b-inv-diff-b-s2-d-p-1-witness p))
                            (cp (choice-set-s2-d-p
                                 (diff-b-s2-d-p-q-witness (b-inv-diff-b-s2-d-p-1-witness p))))
                            (p p))
                 )
           :in-theory nil
           )))

(defthmd diff-b-inv-wb-s2-d-p-equiv
  (iff (diff-b-inv-wb-s2-d-p p)
       (b-inv-diff-b-s2-d-p p))
  :hints (("goal"
           :use ((:instance diff-b-inv-wb-s2-d-p-equiv-1)
                 (:instance diff-b-inv-wb-s2-d-p-equiv-2))
           )))

(defthmd disjoint-lemmas-1-1
  (implies (m-= (m-* m1 m2) (m-* m3 m4))
           (m-= (m-* (m-* m5 m1) m2)
                (m-* (m-* m5 m3) m4))))

(defthmd disjoint-lemmas-1-2
  (implies (and (m-= (m-* (m-* inv-y x) p)
                     (m-* (m-* inv-y y) q))
                (m-= (m-* inv-y x) c-inv-y-x)
                (m-= (m-* inv-y y) id)
                (m-= (m-* id q) q))
           (m-= q (m-* c-inv-y-x p))))

(defthmd disjoint-lemmas-1
  (implies (and (reducedwordp x)
                (reducedwordp y)
                (point-in-r3 p)
                (point-in-r3 q)
                (m-= (m-* (rotation x (acl2-sqrt 2)) p)
                     (m-* (rotation y (acl2-sqrt 2)) q)))
           (m-= q (m-* (rotation (compose (word-inverse y) x) (acl2-sqrt 2)) p)))
  :hints (("goal"
           :use ((:instance disjoint-lemmas-1-1
                            (m1 (rotation x (acl2-sqrt 2)))
                            (m3 (rotation y (acl2-sqrt 2)))
                            (m2 p)
                            (m4 q)
                            (m5 (rotation (word-inverse y) (acl2-sqrt 2))))
                 (:instance rot-a*rot-b-= (a (word-inverse y))
                            (b x)
                            (x (acl2-sqrt 2)))
                 (:instance rot-a*rot-b-= (a (word-inverse y))
                            (b y)
                            (x (acl2-sqrt 2)))
                 (:instance reducedwordp-word-inverse (x y))
                 (:instance reduced-inverse (x (word-inverse y)))
                 (:instance inv-inv-x=x (x y))
                 (:instance reducedwordp=>weak-wordp (x y))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 q))
                 (:instance disjoint-lemmas-1-2 (inv-y (rotation (word-inverse y) (acl2-sqrt 2)))
                            (x (rotation x (acl2-sqrt 2)))
                            (p p)
                            (q q)
                            (y (rotation y (acl2-sqrt 2)))
                            (c-inv-y-x (rotation (compose (word-inverse y) x) (acl2-sqrt 2)))
                            (id (id-rotation)))
                 )
           :in-theory nil
           )))

(defthmd disjoint-lemmas-2
  (implies (and (reducedwordp wx)
                (reducedwordp wy)
                (reducedwordp wa)
                (reducedwordp wb)
                (equal (choice-set-s2-d-p p1) cp1)
                (equal (choice-set-s2-d-p p2) cp2)
                (s2-d-p p1)
                (s2-d-p p2)
                (point-in-r3 p)
                (m-= (m-* (rotation wa (acl2-sqrt 2)) cp1) p)
                (m-= (m-* (rotation wb (acl2-sqrt 2)) cp2) p)
                (m-= (m-* (rotation wx (acl2-sqrt 2)) p1) cp1)
                (m-= (m-* (rotation wy (acl2-sqrt 2)) p2) cp2))
           (and (orbit-point-p-q cp1 p2)
                (orbit-point-p-q cp2 p1)
                (orbit-point-p-q p1 p1)
                (orbit-point-p-q p2 p2)
                (orbit-point-p-q p p)))
  :hints (("goal"
           :use ((:instance orbit-point-p-q-suff (point p) (o-point p) (w nil))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 (:instance orbit-point-p-q-suff (point p1) (o-point p1) (w nil))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance orbit-point-p-q-suff (point p2) (o-point p2) (w nil))
                 (:instance m-*point-id=point (p1 p2))
                 (:instance choice-set-s2-d-p-rewrite (o-p p) (p p))
                 (:instance disjoint-lemmas-1 (x wa) (y wb) (p cp1) (q cp2))
                 (:instance disjoint-lemmas-1 (x wy) (y (compose (word-inverse wb) wa)) (p p2) (q cp1))
                 (:instance disjoint-lemmas-1 (x wb) (y wa) (p cp2) (q cp1))
                 (:instance disjoint-lemmas-1 (x wx) (y (compose (word-inverse wa) wb)) (p p1) (q cp2))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance s2-d-p (point p1))
                 (:instance s2-def-p (point p1))
                 (:instance s2-d-p (point p2))
                 (:instance s2-def-p (point p2))
                 (:instance choice-set-s2-d-p-rewrite (o-p p1) (p p1))
                 (:instance choice-set-s2-d-p-rewrite (o-p p2) (p p2))
                 (:instance reducedwordp-word-inverse (x wa))
                 (:instance reducedwordp-word-inverse (x wb))
                 (:instance closure-prop (x (word-inverse wb)) (y wa))
                 (:instance closure-prop (x (word-inverse wa)) (y wb))
                 (:instance orbit-point-p-q-suff (o-point (choice-set-s2-d-p p2))
                            (point p1)
                            (w (compose (word-inverse (compose (word-inverse wa) wb))
                                        wx)))
                 (:instance reducedwordp-word-inverse (x (compose (word-inverse wa) wb)))
                 (:instance closure-prop (x (word-inverse (compose (word-inverse wa) wb)))
                            (y wx))
                 (:instance orbit-point-p-q-suff (o-point (choice-set-s2-d-p p1))
                            (point p2)
                            (w (compose (word-inverse (compose (word-inverse wb) wa))
                                        wy)))
                 (:instance reducedwordp-word-inverse (x (compose (word-inverse wb) wa)))
                 (:instance closure-prop (x (word-inverse (compose (word-inverse wb) wa)))
                            (y wy))
                 )
           :in-theory nil
           )))

(defthmd disjoint-lemmas-3
  (implies (and (orbit-point-p-q (choice-set-s2-d-p p1) p2)
                (orbit-point-p-q (choice-set-s2-d-p p2) p1))
           (equal (choice-set-s2-d-p p1) (choice-set-s2-d-p p2)))
  :hints (("goal"
           :use ((:instance choice-set-s2-d-p (c-point (choice-set-s2-d-p p1)) (p p1))
                 (:instance choice-set-s2-d-p (c-point (choice-set-s2-d-p p2)) (p p2)))
           :in-theory nil
           )))

(defthmd disjoint-lemmas-4-1
  (implies (equal x y)
           (equal (compose z x) (compose z y))))

(defthmd disjoint-lemmas-4-2
  (implies (reducedwordp x)
           (equal (compose nil x) x))
  :hints (("goal"
           :use ((:instance word-fix=reducedwordp (x x)))
           )))

(defthmd disjoint-lemmas-4-3
  (implies (reducedwordp y)
           (equal (compose y nil) y))
  :hints (("goal"
           :use ((:instance word-fix=reducedwordp (x y)))
           )))

(defthmd disjoint-lemmas-4
  (implies (and (a-wordp x)
                (or (b-wordp y)
                    (a-inv-wordp y)
                    (b-inv-wordp y)
                    (equal y nil)))
           (not (equal (compose (word-inverse y) x) nil)))
  :hints (("goal"
           :use ((:instance assoc-prop (x y) (y (word-inverse y)) (z x))
                 (:instance reducedwordp-word-inverse (x y))
                 (:instance reduced-inverse (x y))
                 (:instance s2-d-p-equiv-2-lemma2 (w y))
                 (:instance s2-d-p-equiv-2-lemma2 (w x))
                 (:instance a-wordp-equivalent (a x))
                 (:instance disjoint-lemmas-4-2)
                 (:instance disjoint-lemmas-4-3)
                 (:instance disjoint-lemmas-4-1 (x (compose (word-inverse y) x)) (y nil)))
           :in-theory nil
           )))

(defthmd disjoint-lemmas-5
  (implies (and (s2-def-p p)
                (word-exists p))
           (d-p p)))

(defthmd disjoint-lemmas-6
  (implies (and (reducedwordp x)
                (reducedwordp y)
                (point-in-r3 p)
                (point-in-r3 q)
                (m-= (m-* (rotation x (acl2-sqrt 2)) p)
                     (m-* (rotation y (acl2-sqrt 2)) q)))
           (m-= (m-* (rotation (compose (word-inverse y) x) (acl2-sqrt 2)) p) q))
  :hints (("goal"
           :use (:instance disjoint-lemmas-1)
           )))

(defthmd disjoint-1
  (implies (diff-a-s2-d-p p)
           (not (diff-b-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-4 (y (diff-b-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-a-s2-d-p (p p))
                 (:instance diff-a-s2-d-p-q-equiv (p p))
                 (:instance diff-a-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-b-s2-d-p (p p))
                 (:instance diff-b-s2-d-p-q-equiv (p p))
                 (:instance diff-b-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                         (diff-a-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                         (diff-b-s2-d-p-q-witness p)))
                            (wa (diff-a-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                           p))
                            (wb (diff-b-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                           p))
                            (p1 (diff-a-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p2 (diff-b-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-s2-d-p-q-witness p))
                            (p (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-s2-d-p-q-witness p)) (o-point (diff-a-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-b-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-a-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-s2-d-p-q-witness p))
                            (p (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-s2-d-p-q-witness p)) (o-point (diff-b-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p (diff-b-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-a-s2-d-p-q-witness p))
                            (p2 (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-a-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                          p))
                            (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                         (diff-a-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-a-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                  (diff-a-s2-d-p-q-witness p)))
                            (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                     (diff-a-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                       (diff-a-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-a-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                           (diff-a-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-b-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                       p))
                                        (diff-a-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-b-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p))
                            (x (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-2
  (implies (diff-a-s2-d-p p)
           (not (diff-a-inv-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-4 (y (diff-a-inv-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-a-s2-d-p (p p))
                 (:instance diff-a-s2-d-p-q-equiv (p p))
                 (:instance diff-a-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-a-inv-s2-d-p (p p))
                 (:instance diff-a-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-a-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                         (diff-a-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                         (diff-a-inv-s2-d-p-q-witness p)))
                            (wa (diff-a-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                           p))
                            (wb (diff-a-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                               p))
                            (p1 (diff-a-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p2 (diff-a-inv-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-s2-d-p-q-witness p))
                            (p (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-s2-d-p-q-witness p)) (o-point (diff-a-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-a-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-a-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-inv-s2-d-p-q-witness p))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-inv-s2-d-p-q-witness p)) (o-point (diff-a-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-a-s2-d-p-q-witness p))
                            (p2 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-a-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                          p))
                            (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                         (diff-a-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-a-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                  (diff-a-s2-d-p-q-witness p)))
                            (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                     (diff-a-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                       (diff-a-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-a-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                           (diff-a-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-a-inv-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                       p))
                                        (diff-a-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-a-inv-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p))
                            (x (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-3
  (implies (diff-a-s2-d-p p)
           (not (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-4 (y (diff-b-inv-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-a-s2-d-p (p p))
                 (:instance diff-a-s2-d-p-q-equiv (p p))
                 (:instance diff-a-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-b-inv-s2-d-p (p p))
                 (:instance diff-b-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-b-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                         (diff-a-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                         (diff-b-inv-s2-d-p-q-witness p)))
                            (wa (diff-a-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                           p))
                            (wb (diff-b-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                               p))
                            (p1 (diff-a-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p2 (diff-b-inv-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-s2-d-p-q-witness p))
                            (p (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-s2-d-p-q-witness p)) (o-point (diff-a-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-b-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-a-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-inv-s2-d-p-q-witness p))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-inv-s2-d-p-q-witness p)) (o-point (diff-b-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-a-s2-d-p-q-witness p))
                            (p2 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-a-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                          p))
                            (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                         (diff-a-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-a-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                  (diff-a-s2-d-p-q-witness p)))
                            (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                     (diff-a-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                       (diff-a-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-a-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                           (diff-a-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-b-inv-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                       p))
                                        (diff-a-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-b-inv-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p))
                            (x (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-4
  (implies (diff-a-s2-d-p p)
           (not (diff-n-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-4 (y (diff-n-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-a-s2-d-p (p p))
                 (:instance diff-a-s2-d-p-q-equiv (p p))
                 (:instance diff-a-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-n-s2-d-p (p p))
                 (:instance diff-n-s2-d-p-q-equiv (p p))
                 (:instance diff-n-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                         (diff-a-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                         (diff-n-s2-d-p-q-witness p)))
                            (wa (diff-a-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                           p))
                            (wb (diff-n-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                           p))
                            (p1 (diff-a-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p2 (diff-n-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-s2-d-p-q-witness p))
                            (p (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-s2-d-p-q-witness p)) (o-point (diff-a-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-n-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-a-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-n-s2-d-p-q-witness p))
                            (p (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-n-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-n-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-n-s2-d-p-q-witness p)) (o-point (diff-n-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p (diff-n-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-a-s2-d-p-q-witness p))
                            (p2 (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-a-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                          p))
                            (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                         (diff-a-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-a-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                  (diff-a-s2-d-p-q-witness p)))
                            (point (diff-a-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                     (diff-a-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                                       (diff-a-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-a-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                                           (diff-a-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-a-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-n-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                       p))
                                        (diff-a-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-n-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-n-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-n-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                p))
                            (x (diff-a-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-a-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-lemmas-7
  (implies (and (b-wordp x)
                (or (a-inv-wordp y)
                    (b-inv-wordp y)
                    (equal y nil)))
           (not (equal (compose (word-inverse y) x) nil)))
  :hints (("goal"
           :use ((:instance assoc-prop (x y) (y (word-inverse y)) (z x))
                 (:instance reducedwordp-word-inverse (x y))
                 (:instance reduced-inverse (x y))
                 (:instance s2-d-p-equiv-2-lemma2 (w y))
                 (:instance s2-d-p-equiv-2-lemma2 (w x))
                 (:instance b-wordp-equivalent (b x))
                 (:instance disjoint-lemmas-4-2)
                 (:instance disjoint-lemmas-4-3)
                 (:instance disjoint-lemmas-4-1 (x (compose (word-inverse y) x)) (y nil)))
           :in-theory nil
           )))

(defthmd disjoint-5
  (implies (diff-b-s2-d-p p)
           (not (diff-a-inv-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-7 (y (diff-a-inv-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-b-s2-d-p (p p))
                 (:instance diff-b-s2-d-p-q-equiv (p p))
                 (:instance diff-b-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-a-inv-s2-d-p (p p))
                 (:instance diff-a-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-a-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                         (diff-b-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                         (diff-a-inv-s2-d-p-q-witness p)))
                            (wa (diff-b-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                           p))
                            (wb (diff-a-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                               p))
                            (p1 (diff-b-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p2 (diff-a-inv-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-s2-d-p-q-witness p))
                            (p (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-s2-d-p-q-witness p)) (o-point (diff-b-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-a-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-b-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-inv-s2-d-p-q-witness p))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-inv-s2-d-p-q-witness p)) (o-point (diff-a-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-b-s2-d-p-q-witness p))
                            (p2 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-b-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                          p))
                            (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                         (diff-b-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-b-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                  (diff-b-s2-d-p-q-witness p)))
                            (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                     (diff-b-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-b-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                       (diff-b-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-b-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                           (diff-b-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-b-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-a-inv-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                       p))
                                        (diff-b-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-a-inv-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p))
                            (x (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-6
  (implies (diff-b-s2-d-p p)
           (not (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-7 (y (diff-b-inv-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-b-s2-d-p (p p))
                 (:instance diff-b-s2-d-p-q-equiv (p p))
                 (:instance diff-b-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-b-inv-s2-d-p (p p))
                 (:instance diff-b-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-b-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                         (diff-b-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                         (diff-b-inv-s2-d-p-q-witness p)))
                            (wa (diff-b-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                           p))
                            (wb (diff-b-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                               p))
                            (p1 (diff-b-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p2 (diff-b-inv-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-s2-d-p-q-witness p))
                            (p (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-s2-d-p-q-witness p)) (o-point (diff-b-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-b-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-b-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-inv-s2-d-p-q-witness p))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-inv-s2-d-p-q-witness p)) (o-point (diff-b-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-b-s2-d-p-q-witness p))
                            (p2 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-b-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                          p))
                            (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                         (diff-b-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-b-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                  (diff-b-s2-d-p-q-witness p)))
                            (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                     (diff-b-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-b-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                       (diff-b-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-b-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                           (diff-b-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-b-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-b-inv-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                       p))
                                        (diff-b-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-b-inv-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p))
                            (x (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-7
  (implies (diff-b-s2-d-p p)
           (not (diff-n-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-7 (y (diff-n-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-b-s2-d-p (p p))
                 (:instance diff-b-s2-d-p-q-equiv (p p))
                 (:instance diff-b-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-n-s2-d-p (p p))
                 (:instance diff-n-s2-d-p-q-equiv (p p))
                 (:instance diff-n-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                         (diff-b-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                         (diff-n-s2-d-p-q-witness p)))
                            (wa (diff-b-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                           p))
                            (wb (diff-n-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                           p))
                            (p1 (diff-b-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p2 (diff-n-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-s2-d-p-q-witness p))
                            (p (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-s2-d-p-q-witness p)) (o-point (diff-b-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-n-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-b-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-n-s2-d-p-q-witness p))
                            (p (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-n-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-n-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-n-s2-d-p-q-witness p)) (o-point (diff-n-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p (diff-n-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-b-s2-d-p-q-witness p))
                            (p2 (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-b-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                          p))
                            (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                         (diff-b-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-b-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                  (diff-b-s2-d-p-q-witness p)))
                            (point (diff-b-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                     (diff-b-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-b-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                                       (diff-b-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-b-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                                           (diff-b-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-b-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-n-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                       p))
                                        (diff-b-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-n-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-n-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-n-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                p))
                            (x (diff-b-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-b-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-lemmas-8
  (implies (and (a-inv-wordp x)
                (or (b-inv-wordp y)
                    (equal y nil)))
           (not (equal (compose (word-inverse y) x) nil)))
  :hints (("goal"
           :use ((:instance assoc-prop (x y) (y (word-inverse y)) (z x))
                 (:instance reducedwordp-word-inverse (x y))
                 (:instance reduced-inverse (x y))
                 (:instance s2-d-p-equiv-2-lemma2 (w y))
                 (:instance s2-d-p-equiv-2-lemma2 (w x))
                 (:instance a-inv-wordp-equivalent (a-inv x))
                 (:instance disjoint-lemmas-4-2)
                 (:instance disjoint-lemmas-4-3)
                 (:instance disjoint-lemmas-4-1 (x (compose (word-inverse y) x)) (y nil)))
           :in-theory nil
           )))

(defthmd disjoint-8
  (implies (diff-a-inv-s2-d-p p)
           (not (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-8 (y (diff-b-inv-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-a-inv-s2-d-p (p p))
                 (:instance diff-a-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-a-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-b-inv-s2-d-p (p p))
                 (:instance diff-b-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-b-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                         (diff-a-inv-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                         (diff-b-inv-s2-d-p-q-witness p)))
                            (wa (diff-a-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                               p))
                            (wb (diff-b-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                               p))
                            (p1 (diff-a-inv-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p2 (diff-b-inv-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-inv-s2-d-p-q-witness p))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-inv-s2-d-p-q-witness p)) (o-point (diff-a-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-b-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-a-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-inv-s2-d-p-q-witness p))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-inv-s2-d-p-q-witness p)) (o-point (diff-b-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-a-inv-s2-d-p-q-witness p))
                            (p2 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-a-inv-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                          p))
                            (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                                         (diff-a-inv-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-a-inv-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                                  (diff-a-inv-s2-d-p-q-witness p)))
                            (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                                     (diff-a-inv-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                                       (diff-a-inv-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                           (diff-a-inv-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-b-inv-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                       p))
                                        (diff-a-inv-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-b-inv-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p))
                            (x (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-9
  (implies (diff-a-inv-s2-d-p p)
           (not (diff-n-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-8 (y (diff-n-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-a-inv-s2-d-p (p p))
                 (:instance diff-a-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-a-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-n-s2-d-p (p p))
                 (:instance diff-n-s2-d-p-q-equiv (p p))
                 (:instance diff-n-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                         (diff-a-inv-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                         (diff-n-s2-d-p-q-witness p)))
                            (wa (diff-a-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                               p))
                            (wb (diff-n-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                           p))
                            (p1 (diff-a-inv-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p2 (diff-n-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-inv-s2-d-p-q-witness p))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-inv-s2-d-p-q-witness p)) (o-point (diff-a-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-n-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-a-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-n-s2-d-p-q-witness p))
                            (p (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-n-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-n-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-n-s2-d-p-q-witness p)) (o-point (diff-n-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p (diff-n-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-a-inv-s2-d-p-q-witness p))
                            (p2 (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-a-inv-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                          p))
                            (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                                         (diff-a-inv-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-a-inv-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                                  (diff-a-inv-s2-d-p-q-witness p)))
                            (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                                     (diff-a-inv-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                                       (diff-a-inv-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                           (diff-a-inv-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-n-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                       p))
                                        (diff-a-inv-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-n-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-n-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-n-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                p))
                            (x (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-lemmas-9
  (implies (and (b-inv-wordp x)
                (or (a-inv-wordp y)
                    (equal y nil)))
           (not (equal (compose (word-inverse y) x) nil)))
  :hints (("goal"
           :use ((:instance assoc-prop (x y) (y (word-inverse y)) (z x))
                 (:instance reducedwordp-word-inverse (x y))
                 (:instance reduced-inverse (x y))
                 (:instance s2-d-p-equiv-2-lemma2 (w y))
                 (:instance s2-d-p-equiv-2-lemma2 (w x))
                 (:instance b-inv-wordp-equivalent (b-inv x))
                 (:instance disjoint-lemmas-4-2)
                 (:instance disjoint-lemmas-4-3)
                 (:instance disjoint-lemmas-4-1 (x (compose (word-inverse y) x)) (y nil)))
           :in-theory nil
           )))


(defthmd disjoint-10
  (implies (diff-b-inv-s2-d-p p)
           (not (diff-n-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-9 (y (diff-n-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                  p))
                            (x (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-b-inv-s2-d-p (p p))
                 (:instance diff-b-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-b-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-n-s2-d-p (p p))
                 (:instance diff-n-s2-d-p-q-equiv (p p))
                 (:instance diff-n-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                         (diff-b-inv-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                         (diff-n-s2-d-p-q-witness p)))
                            (wa (diff-b-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                               p))
                            (wb (diff-n-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                           p))
                            (p1 (diff-b-inv-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p2 (diff-n-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-inv-s2-d-p-q-witness p))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-inv-s2-d-p-q-witness p)) (o-point (diff-b-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-n-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                      p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-b-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                      p)))

                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-n-s2-d-p-q-witness p))
                            (p (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-n-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-n-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-n-s2-d-p-q-witness p)) (o-point (diff-n-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p)))
                            (p (diff-n-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-b-inv-s2-d-p-q-witness p))
                            (p2 (diff-n-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-b-inv-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                          p))
                            (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                                         (diff-b-inv-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-b-inv-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                                  (diff-b-inv-s2-d-p-q-witness p)))
                            (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                                     (diff-b-inv-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-b-inv-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                                       (diff-b-inv-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-b-inv-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                           (diff-b-inv-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-b-inv-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-n-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                       p))
                                        (diff-b-inv-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-n-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-n-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-n-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p))
                                p))
                            (x (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-lemmas-10
  (implies (and (equal x nil)
                (or (a-inv-wordp y)
                    (b-inv-wordp y)
                    (a-wordp y)
                    (b-wordp y)))
           (not (equal (compose (word-inverse y) x) nil)))
  :hints (("goal"
           :use ((:instance assoc-prop (x y) (y (word-inverse y)) (z x))
                 (:instance reducedwordp-word-inverse (x y))
                 (:instance reduced-inverse (x y))
                 (:instance s2-d-p-equiv-2-lemma2 (w y))
                 (:instance s2-d-p-equiv-2-lemma2 (w x))
                 (:instance b-inv-wordp-equivalent (b-inv y))
                 (:instance a-inv-wordp-equivalent (a-inv y))
                 (:instance a-wordp-equivalent (a y))
                 (:instance b-wordp-equivalent (b y))
                 (:instance disjoint-lemmas-4-2)
                 (:instance disjoint-lemmas-4-3)
                 (:instance disjoint-lemmas-4-1 (x (compose (word-inverse y) x)) (y nil)))
           :in-theory nil
           )))

(defthmd disjoint-lemmas-11
  (implies (and (a-inv*w-a-p x)
                (a-inv-wordp y))
           (not (equal (compose (word-inverse y) x) nil)))
  :hints (("goal"
           :use ((:instance assoc-prop (x y) (y (word-inverse y)) (z x))
                 (:instance reducedwordp-word-inverse (x y))
                 (:instance reduced-inverse (x y))
                 (:instance s2-d-p-equiv-2-lemma2 (w y))
                 (:instance s2-d-p-equiv-2-lemma2 (w x))
                 (:instance a-wordp-equivalent (a x))
                 (:instance disjoint-lemmas-4-2)
                 (:instance disjoint-lemmas-4-3)
                 (:instance disjoint-lemmas-4-1 (x (compose (word-inverse y) x)) (y nil))
                 (:instance a-inv*w-a-p-equiv (w x))
                 (:instance disjoint-lemmas-4 (x x) (y y))
                 (:instance not-wa-inv-p (w x))
                 (:instance disjoint-lemmas-9 (x x) (y y))
                 (:instance disjoint-lemmas-10 (x x) (y y))
                 (:instance disjoint-lemmas-7 (x x)))
           :in-theory nil
           )))

(defthmd disjoint-11-1
  (implies (diff-a-inv-wa-s2-d-p p)
           (not (diff-a-inv-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-11 (y (diff-a-inv-s2-d-p-q-1-witness
                                                   (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                   p))
                            (x (diff-a-inv-wa-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-a-inv-wa-s2-d-p (p p))
                 (:instance diff-a-inv-wa-s2-d-p-q-equiv (p p))
                 (:instance diff-a-inv-wa-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-a-inv-s2-d-p (p p))
                 (:instance diff-a-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-a-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                         (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                         (diff-a-inv-s2-d-p-q-witness p)))
                            (wa (diff-a-inv-wa-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                                  p))
                            (wb (diff-a-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                               p))
                            (p1 (diff-a-inv-wa-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (p2 (diff-a-inv-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-inv-wa-s2-d-p-q-witness p))
                            (p (diff-a-inv-wa-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-inv-wa-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-inv-wa-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-inv-wa-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-inv-wa-s2-d-p-q-witness p)) (o-point (diff-a-inv-wa-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (p (diff-a-inv-wa-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-a-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                      p)))
                 (:instance diff-s2-d-p-=-4-1 (w (diff-a-inv-wa-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                  p)))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-a-inv-s2-d-p-q-witness p))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-a-inv-s2-d-p-q-witness p)) (o-point (diff-a-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p)))
                            (p (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-a-inv-wa-s2-d-p-q-witness p))
                            (p2 (diff-a-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-a-inv-wa-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                          p))
                            (point (diff-a-inv-wa-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                                         (diff-a-inv-wa-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                                  (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (point (diff-a-inv-wa-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                                     (diff-a-inv-wa-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-a-inv-wa-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                                       (diff-a-inv-wa-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-a-inv-wa-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                                           (diff-a-inv-wa-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-a-inv-wa-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-a-inv-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                       p))
                                        (diff-a-inv-wa-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-a-inv-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-a-inv-wa-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-a-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-s2-d-p-q-witness p))
                                p))
                            (x (diff-a-inv-wa-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-a-inv-wa-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-11
  (implies (a-inv-diff-a-s2-d-p p)
           (not (diff-a-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance disjoint-11-1)
                 (:instance diff-a-inv-wa-s2-d-p-equiv))
           )))

(defthmd disjoint-lemmas-12
  (implies (and (b-inv*w-b-p x)
                (b-inv-wordp y))
           (not (equal (compose (word-inverse y) x) nil)))
  :hints (("goal"
           :use ((:instance assoc-prop (x y) (y (word-inverse y)) (z x))
                 (:instance reducedwordp-word-inverse (x y))
                 (:instance reduced-inverse (x y))
                 (:instance s2-d-p-equiv-2-lemma2 (w y))
                 (:instance s2-d-p-equiv-2-lemma2 (w x))
                 (:instance a-wordp-equivalent (a x))
                 (:instance disjoint-lemmas-4-2)
                 (:instance disjoint-lemmas-4-3)
                 (:instance disjoint-lemmas-4-1 (x (compose (word-inverse y) x)) (y nil))
                 (:instance b-inv*w-b-p-equiv (w x))
                 (:instance disjoint-lemmas-4 (x x) (y y))
                 (:instance not-wb-inv-p (w x))
                 (:instance disjoint-lemmas-9 (x x) (y y))
                 (:instance disjoint-lemmas-10 (x x) (y y))
                 (:instance disjoint-lemmas-7 (x x)))
           :in-theory nil
           )))

(defthmd disjoint-12-1
  (implies (diff-b-inv-wb-s2-d-p p)
           (not (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use (
                 (:instance disjoint-lemmas-12 (y (diff-b-inv-s2-d-p-q-1-witness
                                                   (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                   p))
                            (x (diff-b-inv-wb-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                p)))
                 (:instance diff-b-inv-wb-s2-d-p (p p))
                 (:instance diff-b-inv-wb-s2-d-p-q-equiv (p p))
                 (:instance diff-b-inv-wb-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (p p))
                 (:instance diff-b-inv-s2-d-p (p p))
                 (:instance diff-b-inv-s2-d-p-q-equiv (p p))
                 (:instance diff-b-inv-s2-d-p-q-1-equiv (cp1 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance disjoint-lemmas-2
                            (wx (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                         (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (wy (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                         (diff-b-inv-s2-d-p-q-witness p)))
                            (wa (diff-b-inv-wb-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                                  p))
                            (wb (diff-b-inv-s2-d-p-q-1-witness (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                               p))
                            (p1 (diff-b-inv-wb-s2-d-p-q-witness p))
                            (cp1 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (p2 (diff-b-inv-s2-d-p-q-witness p))
                            (cp2 (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p p))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-inv-wb-s2-d-p-q-witness p))
                            (p (diff-b-inv-wb-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-inv-wb-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-inv-wb-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-inv-wb-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-inv-wb-s2-d-p-q-witness p)) (o-point (diff-b-inv-wb-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (p (diff-b-inv-wb-s2-d-p-q-witness p)))
                 (:instance s2-d-p-equiv-2-lemma2 (w (diff-b-inv-s2-d-p-q-1-witness
                                                      (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                      p)))
                 (:instance diff-s2-d-p-=-6-1 (w (diff-b-inv-wb-s2-d-p-q-1-witness
                                                  (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                  p)))
                 (:instance choice-set-s2-d-p-rewrite
                            (o-p (diff-b-inv-s2-d-p-q-witness p))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-def-p (point (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance rotation (w nil) (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance orbit-point-p-q-suff (point (diff-b-inv-s2-d-p-q-witness p)) (o-point (diff-b-inv-s2-d-p-q-witness p)) (w nil))
                 (:instance s2-d-p-equiv-2-lemma2 (w nil))
                 (:instance orbit-point-p-q-equiv
                            (o-p (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p)))
                            (p (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance disjoint-lemmas-3 (p1 (diff-b-inv-wb-s2-d-p-q-witness p))
                            (p2 (diff-b-inv-s2-d-p-q-witness p)))
                 (:instance s2-d-p=>p (w (diff-b-inv-wb-s2-d-p-q-1-witness
                                          (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                          p))
                            (point (diff-b-inv-wb-s2-d-p-q-witness p)))
                 (:instance s2-def-p-p=>p1 (p (m-*
                                               (rotation
                                                (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                                         (diff-b-inv-wb-s2-d-p-q-witness p))
                                                (acl2-sqrt 2))
                                               (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (p1 (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))))
                 (:instance s2-d-p=>p (w (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                                  (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (point (diff-b-inv-wb-s2-d-p-q-witness p)))
                 (:instance s2-d-p (point (m-*
                                           (rotation
                                            (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                                     (diff-b-inv-wb-s2-d-p-q-witness p))
                                            (acl2-sqrt 2))
                                           (diff-b-inv-wb-s2-d-p-q-witness p))))
                 (:instance s2-def-p (point (m-*
                                             (rotation
                                              (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                                       (diff-b-inv-wb-s2-d-p-q-witness p))
                                              (acl2-sqrt 2))
                                             (diff-b-inv-wb-s2-d-p-q-witness p))))
                 (:instance d-p-p=>d-p-p1-1 (p (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (p1 (m-*
                                 (rotation
                                  (orbit-point-p-q-witness (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                                           (diff-b-inv-wb-s2-d-p-q-witness p))
                                  (acl2-sqrt 2))
                                 (diff-b-inv-wb-s2-d-p-q-witness p))))
                 (:instance s2-def-p-equiv (p (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))))
                 (:instance word-exists-suff
                            (w (compose (word-inverse (diff-b-inv-s2-d-p-q-1-witness
                                                       (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                       p))
                                        (diff-b-inv-wb-s2-d-p-q-1-witness
                                         (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                         p)))
                            (point (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))))
                 (:instance closure-prop (x (word-inverse (diff-b-inv-s2-d-p-q-1-witness
                                                           (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                                           p)))
                            (y (diff-b-inv-wb-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                p)))
                 (:instance reducedwordp-word-inverse
                            (x (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p)))
                 (:instance disjoint-lemmas-6
                            (y (diff-b-inv-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-s2-d-p-q-witness p))
                                p))
                            (x (diff-b-inv-wb-s2-d-p-q-1-witness
                                (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))
                                p))
                            (p (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p)))
                            (q (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))))
                 (:instance disjoint-lemmas-5 (p (choice-set-s2-d-p (diff-b-inv-wb-s2-d-p-q-witness p))))

                 )
           :in-theory nil
           )))

(defthmd disjoint-12
  (implies (b-inv-diff-b-s2-d-p p)
           (not (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance disjoint-12-1)
                 (:instance diff-b-inv-wb-s2-d-p-equiv))
           )))

(defthmd s2-d-p-equivalence-1
  (iff (s2-d-p p)
       (or (diff-n-s2-d-p p)
           (diff-a-s2-d-p p)
           (diff-a-inv-s2-d-p p)
           (diff-b-s2-d-p p)
           (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance s2-d-p-equiv (p p))
                 (:instance diff-s2-d-p-equivalence-1 (p p)))
           )))

(defthmd s2-d-p-equivalence-2
  (iff (s2-d-p p)
       (or (a-inv-diff-a-s2-d-p p)
           (diff-a-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance s2-d-p-equiv (p p))
                 (:instance diff-s2-d-p-equivalence-2 (p p))
                 (:instance diff-a-inv-wa-s2-d-p-equiv))
           )))

(defthmd s2-d-p-equivalence-3
  (iff (s2-d-p p)
       (or (b-inv-diff-b-s2-d-p p)
           (diff-b-inv-s2-d-p p)))
  :hints (("goal"
           :use ((:instance s2-d-p-equiv (p p))
                 (:instance diff-b-inv-wb-s2-d-p-equiv)
                 (:instance diff-s2-d-p-equivalence-3 (p p)))
           )))
