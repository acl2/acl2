; Banach-Tarski theorem
;
; A free group of 3-d matrices of rank 2.
; See rotations.lisp for the proof that every element of this free group is
; a rotation.
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

(include-book "workshops/2003/cowles-gamboa-van-baalen_matrix/support/matalg" :dir :system)
(include-book "nonstd/nsa/sqrt" :dir :system)
(include-book "groups")

(defun id-rotation ()
  '((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1)
    ((0 . 1) . 0)
    ((0 . 2) . 0)
    ((1 . 0) . 0)
    ((1 . 1) . 1)
    ((1 . 2) . 0)
    ((2 . 0) . 0)
    ((2 . 1) . 0)
    ((2 . 2) . 1)
    )
  )

(defun a-rotation (x)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1)
    ((0 . 1) . 0)
    ((0 . 2) . 0)
    ((1 . 0) . 0)
    ((1 . 1) . 1/3)
    ((1 . 2) . ,(* -2/3 x) )
    ((2 . 0) . 0)
    ((2 . 1) . ,(* 2/3 x) )
    ((2 . 2) . 1/3)
    )
  )

(defun a-inv-rotation (x)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1)
    ((0 . 1) . 0)
    ((0 . 2) . 0)
    ((1 . 0) . 0)
    ((1 . 1) . 1/3)
    ((1 . 2) . ,(* 2/3 x) )
    ((2 . 0) . 0)
    ((2 . 1) . ,(* -2/3 x) )
    ((2 . 2) . 1/3)
    )
  )

(defun b-rotation (x)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1/3)
    ((0 . 1) . ,(* -2/3 x) )
    ((0 . 2) . 0)
    ((1 . 0) . ,(* 2/3 x) )
    ((1 . 1) . 1/3)
    ((1 . 2) . 0)
    ((2 . 0) . 0)
    ((2 . 1) . 0)
    ((2 . 2) . 1)
    )
  )

(defun b-inv-rotation (x)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . 1/3)
    ((0 . 1) . ,(* 2/3 x) )
    ((0 . 2) . 0)
    ((1 . 0) . ,(* -2/3 x) )
    ((1 . 1) . 1/3)
    ((1 . 2) . 0)
    ((2 . 0) . 0)
    ((2 . 1) . 0)
    ((2 . 2) . 1)
    )
  )

(defun point-p ()
  '((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . 0)
    ((1 . 0) . 1)
    ((2 . 0) . 0)
    )
  )


(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm compress21-lemma
     (equal (compress21 name l n i j default)
            (if (zp (- i n)) nil
              (append (compress211 name l n 0 j default)
                      (compress21 name l (+ n 1) i j default))))
     :hints (("goal"
              :in-theory (enable compress21 compress211)
              ))
     )
   )

  (local
   (defthm m-=-row-1-lemma
     (equal (m-=-row-1 m1 m2 m n)
            (if (zp m)
                (m-=-row m1 m2 0 n)
              (and (m-=-row m1 m2 m n)
                   (m-=-row-1 m1 m2 (- m 1) n))))
     )
   )

  (local
   (defthm m-=-row-lemma
     (equal (m-=-row m1 m2 m n)
            (if (zp n)
                (equal (fix (aref2 '$arg1 m1 m 0))
                       (fix (aref2 '$arg2 m2 m 0)))
              (and (equal (fix (aref2 '$arg1 m1 m n))
                          (fix (aref2 '$arg2 m2 m n)))
                   (m-=-row m1 m2 m (- n 1)))))
     )
   )

  (defthmd funs-lemmas-1
    (and (m-= (m-* (id-rotation) (a-rotation x)) (a-rotation x))
         (m-= (m-* (id-rotation) (a-inv-rotation x)) (a-inv-rotation x))
         (m-= (m-* (id-rotation) (b-rotation x)) (b-rotation x))
         (m-= (m-* (id-rotation) (b-inv-rotation x)) (b-inv-rotation x))
         (m-= (m-* (a-rotation x) (id-rotation)) (a-rotation x))
         (m-= (m-* (a-inv-rotation x) (id-rotation)) (a-inv-rotation x))
         (m-= (m-* (b-rotation x) (id-rotation)) (b-rotation x))
         (m-= (m-* (b-inv-rotation x) (id-rotation)) (b-inv-rotation x))
         )
    :hints (("goal"
             :in-theory (enable
                         alist2p array2p aset2 aref2 compress2 header
                         dimensions maximum-length default
                         matrixp compress21
                         m-=
                         m-0
                         m-1
                         m-trans
                         m-unary--
                         s-*
                         m-binary-+
                         m-binary-*
                         m-/
                         m-singularp
                         m-binary-*-row-1
                         m-=-row-1
                         m-=-row)
             )
            )
    )

  (defthmd array2p-funs
    (implies (symbolp y)
             (and (array2p y (id-rotation))
                  (array2p y (a-rotation x))
                  (array2p y (a-inv-rotation x))
                  (array2p y (b-rotation x))
                  (array2p y (b-inv-rotation x))
                  (array2p y (point-p))
                  (equal (first (dimensions y (id-rotation))) 3)
                  (equal (second (dimensions y (id-rotation))) 3)
                  (equal (first (dimensions y (a-rotation x))) 3)
                  (equal (second (dimensions y (a-rotation x))) 3)
                  (equal (first (dimensions y (a-inv-rotation x))) 3)
                  (equal (second (dimensions y (a-inv-rotation x))) 3)
                  (equal (first (dimensions y (b-rotation x))) 3)
                  (equal (second (dimensions y (b-rotation x))) 3)
                  (equal (first (dimensions y (b-inv-rotation x))) 3)
                  (equal (second (dimensions y (b-inv-rotation x))) 3)
                  (equal (first (dimensions y (point-p))) 3)
                  (equal (second (dimensions y (point-p))) 1)
                  )
             )
    :hints (("goal"
             :in-theory (enable array2p dimensions header maximum-length)
             ))
    )

  (defthmd
    dimensions-array2p-m-*
    (implies (and (array2p name m1)
                  (array2p name m2)
                  (equal (first (dimensions name m1)) 3)
                  (equal (second (dimensions name m1)) 3)
                  (equal (first (dimensions name m2)) 3)
                  (equal (second (dimensions name m2)) 3))
             (equal (dimensions name (m-* m1 m2))
                    (list (first (dimensions name m1))
                          (second (dimensions name m2)))))
    )

  (defthmd
    dimensions-array2p-m-*-1
    (implies (and (array2p name m1)
                  (array2p name m2)
                  (equal (first (dimensions name m1)) 3)
                  (equal (second (dimensions name m1)) 3)
                  (equal (first (dimensions name m2)) 3)
                  (equal (second (dimensions name m2)) 1))
             (equal (dimensions name (m-* m1 m2))
                    (list (first (dimensions name m1))
                          (second (dimensions name m2)))))
    )


  (defun rotation (w x)
    (cond ((atom w) (id-rotation))
          ((equal (car w) (wa)) (m-* (a-rotation x) (rotation (cdr w) x)))
          ((equal (car w) (wa-inv)) (m-* (a-inv-rotation x) (rotation (cdr w) x)))
          ((equal (car w) (wb)) (m-* (b-rotation x) (rotation (cdr w) x)))
          ((equal (car w) (wb-inv)) (m-* (b-inv-rotation x) (rotation (cdr w) x)))
          )
    )

  (defthmd rotation-=
    (implies (and (weak-wordp w)
                  (not (atom w)))
             (cond
              ((equal (car w) (wa)) (equal (rotation w x) (m-* (a-rotation x) (rotation (cdr w) x))))
              ((equal (car w) (wa-inv)) (equal (rotation w x) (m-* (a-inv-rotation x) (rotation (cdr w) x))))
              ((equal (car w) (wb)) (equal (rotation w x) (m-* (b-rotation x) (rotation (cdr w) x))))
              ((equal (car w) (wb-inv)) (equal (rotation w x) (m-* (b-inv-rotation x) (rotation (cdr w) x))))
              )
             ))

  (defthmd rotation-props-ind-case-0
    (implies
     (and (not (atom w))
          (implies (and (weak-wordp (cdr w))
                        (symbolp name))
                   (and (array2p name (rotation (cdr w) x))
                        (equal (car (dimensions name (rotation (cdr w) x)))
                               3)
                        (equal (cadr (dimensions name (rotation (cdr w) x)))
                               3))))
     (implies (and (weak-wordp w)
                   (symbolp name))
              (array2p name (rotation w x))
              ))
    :hints (("goal"
             :use (
                   (:instance rotation-= (w w) (x x))
                   (:instance weak-word-cdr (x w))
                   )
             :in-theory nil
             )
            ("subgoal 4"
             :use ((:instance array2p-m-*
                              (name name)
                              (m2 (rotation (cdr w) x))
                              (m1 (a-rotation x)))
                   (:instance array2p-funs (y name) (x x))
                   )
             )
            ("subgoal 3"
             :use ((:instance array2p-m-*
                              (name name)
                              (m2 (rotation (cdr w) x))
                              (m1 (a-inv-rotation x)))
                   (:instance array2p-funs (y name) (x x))
                   )
             )
            ("subgoal 2"
             :use ((:instance array2p-m-*
                              (name name)
                              (m2 (rotation (cdr w) x))
                              (m1 (b-rotation x)))
                   (:instance array2p-funs (y name) (x x))
                   )
             )
            ("subgoal 1"
             :use ((:instance array2p-m-*
                              (name name)
                              (m2 (rotation (cdr w) x))
                              (m1 (b-inv-rotation x)))
                   (:instance array2p-funs (y name) (x x))
                   )
             )
            )
    )

  (defthmd rotation-props-ind-case-1
    (implies
     (and (not (atom w))
          (implies (and (weak-wordp (cdr w))
                        (symbolp name))
                   (and (array2p name (rotation (cdr w) x))
                        (equal (car (dimensions name (rotation (cdr w) x)))
                               3)
                        (equal (cadr (dimensions name (rotation (cdr w) x)))
                               3))))
     (implies (and (weak-wordp w)
                   (symbolp name))
              (and
               (equal (car (dimensions name (rotation w x)))
                      3)
               (equal (cadr (dimensions name (rotation w x)))
                      3)
               )))
    :hints (("goal"
             :use (
                   (:instance rotation-= (w w) (x x))
                   (:instance weak-word-cdr (x w))
                   )
             :in-theory nil
             )
            ("subgoal 8"
             :use ((:instance dimensions-array2p-m-*
                              (m1 (a-rotation x))
                              (m2 (rotation (cdr w) x)))
                   (:instance array2p-funs (y name) (x x)))
             )
            ("subgoal 7"
             :use ((:instance dimensions-array2p-m-*
                              (m1 (a-rotation x))
                              (m2 (rotation (cdr w) x)))
                   (:instance array2p-funs (y name) (x x)))
             )
            ("subgoal 6"
             :use ((:instance dimensions-array2p-m-*
                              (m1 (a-inv-rotation x))
                              (m2 (rotation (cdr w) x)))
                   (:instance array2p-funs (y name) (x x)))
             )
            ("subgoal 5"
             :use ((:instance dimensions-array2p-m-*
                              (m1 (a-inv-rotation x))
                              (m2 (rotation (cdr w) x)))
                   (:instance array2p-funs (y name) (x x)))
             )
            ("subgoal 4"
             :use ((:instance dimensions-array2p-m-*
                              (m1 (b-rotation x))
                              (m2 (rotation (cdr w) x)))
                   (:instance array2p-funs (y name) (x x)))
             )
            ("subgoal 3"
             :use ((:instance dimensions-array2p-m-*
                              (m1 (b-rotation x))
                              (m2 (rotation (cdr w) x)))
                   (:instance array2p-funs (y name) (x x)))
             )
            ("subgoal 2"
             :use ((:instance dimensions-array2p-m-*
                              (m1 (b-inv-rotation x))
                              (m2 (rotation (cdr w) x)))
                   (:instance array2p-funs (y name) (x x)))
             )
            ("subgoal 1"
             :use ((:instance dimensions-array2p-m-*
                              (m1 (b-inv-rotation x))
                              (m2 (rotation (cdr w) x)))
                   (:instance array2p-funs (y name) (x x)))
             )
            )
    )

  (defthmd rotation-props
    (implies (and (weak-wordp w)
                  (symbolp name))
             (and (array2p name (rotation w x))
                  (equal (first (dimensions name (rotation w x))) 3)
                  (equal (second (dimensions name (rotation w x))) 3))
             )
    :hints (("subgoal *1/5"
             :use ((:instance rotation-props-ind-case-0)
                   (:instance rotation-props-ind-case-1))
             )
            ("subgoal *1/4"
             :use ((:instance rotation-props-ind-case-0)
                   (:instance rotation-props-ind-case-1))
             )
            ("subgoal *1/3"
             :use ((:instance rotation-props-ind-case-0)
                   (:instance rotation-props-ind-case-1))
             )
            ("subgoal *1/2"
             :use ((:instance rotation-props-ind-case-0)
                   (:instance rotation-props-ind-case-1))
             )
            ("subgoal *1/1"
             :in-theory (enable dimensions header maximum-length)
             )
            )
    )

  (defthmd m-*-rotation-point-dim
    (implies (and (weak-wordp w)
                  (symbolp name))
             (and (array2p name (m-* (rotation w x) (point-p)))
                  (equal (first (dimensions name (m-* (rotation w x) (point-p)))) 3)
                  (equal (second (dimensions name (m-* (rotation w x) (point-p)))) 1))
             )
    :hints (("goal"
             :use ((:instance rotation-props (w w) (x x) (name name))
                   (:instance dimensions-array2p-m-*-1
                              (m1 (rotation w x))
                              (m2 (point-p))
                              (name name))
                   (:instance array2p-funs
                              (y name))
                   )
             :in-theory (disable rotation)
             ))
    )

  (defun int-point (a i j n x)
    (cond ((and (equal i 0) (equal j 0)) (* (/ (aref2 '$arg1 a i j) x) (expt 3 n)))
          ((and (equal i 2) (equal j 0)) (* (/ (aref2 '$arg1 a i j) x) (expt 3 n)))
          ((and (equal i 1) (equal j 0)) (* (aref2 '$arg1 a i j) (expt 3 n)))
          (t nil))
    )

  (defthmd rotation-values-ind-case-lemma1-1
    (implies (and (symbolp name)
                  (acl2-numberp (aref2 name m1 0 0))
                  (acl2-numberp (aref2 name m1 1 0))
                  (acl2-numberp (aref2 name m1 2 0)))
             (and (acl2-numberp (aref2 '$arg1 m1 0 0))
                  (acl2-numberp (aref2 '$arg1 m1 1 0))
                  (acl2-numberp (aref2 '$arg1 m1 2 0))
                  (acl2-numberp (aref2 '$arg2 m1 0 0))
                  (acl2-numberp (aref2 '$arg2 m1 1 0))
                  (acl2-numberp (aref2 '$arg2 m1 2 0)))

             )
    :hints (("goal"
             :in-theory (enable aref2 default header)
             ))

    )

  (defthmd rotation-values-ind-case-lemma1
    (implies (and (symbolp name)
                  (acl2-numberp (aref2 name m1 0 0))
                  (acl2-numberp (aref2 name m1 1 0))
                  (acl2-numberp (aref2 name m1 2 0))
                  (acl2-numberp x)
                  (array2p name m1)
                  (equal (first (dimensions name m1)) 3)
                  (equal (second (dimensions name m1)) 1))
             (and (equal (aref2 name (m-* (a-rotation x) m1) 0 0) (aref2 name m1 0 0))
                  (equal (aref2 name (m-* (a-rotation x) m1) 1 0) (/ (- (aref2 name m1 1 0) (* 2 x (aref2 name m1 2 0))) 3))
                  (equal (aref2 name (m-* (a-rotation x) m1) 2 0) (/ (+ (* 2 x (aref2 name m1 1 0)) (aref2 name m1 2 0)) 3))
                  (equal (aref2 name (m-* (a-inv-rotation x) m1) 0 0) (aref2 name m1 0 0))
                  (equal (aref2 name (m-* (a-inv-rotation x) m1) 1 0) (/ (+ (aref2 name m1 1 0) (* 2 x (aref2 name m1 2 0))) 3))
                  (equal (aref2 name (m-* (a-inv-rotation x) m1) 2 0) (/ (- (aref2 name m1 2 0) (* 2 x (aref2 name m1 1 0))) 3))
                  (equal (aref2 name (m-* (b-rotation x) m1) 0 0) (/ (- (aref2 name m1 0 0) (* 2 x (aref2 name m1 1 0))) 3))
                  (equal (aref2 name (m-* (b-rotation x) m1) 1 0) (/ (+ (aref2 name m1 1 0) (* 2 x (aref2 name m1 0 0))) 3))
                  (equal (aref2 name (m-* (b-rotation x) m1) 2 0) (aref2 name m1 2 0))
                  (equal (aref2 name (m-* (b-inv-rotation x) m1) 0 0) (/ (+ (aref2 name m1 0 0) (* 2 x (aref2 name m1 1 0))) 3))
                  (equal (aref2 name (m-* (b-inv-rotation x) m1) 1 0) (/ (- (aref2 name m1 1 0) (* 2 x (aref2 name m1 0 0))) 3))
                  (equal (aref2 name (m-* (b-inv-rotation x) m1) 2 0) (aref2 name m1 2 0)))
             )
    :hints (("goal"
             :use (
                   (:instance array2p-funs (y name))
                   (:instance array2p-alist2p (name name) (l m1))
                   (:instance array2p-alist2p (name name) (l (a-rotation x)))
                   (:instance array2p-alist2p (name name) (l (a-inv-rotation x)))
                   (:instance array2p-alist2p (name name) (l (b-rotation x)))
                   (:instance array2p-alist2p (name name) (l (b-inv-rotation x)))
                   (:instance rotation-values-ind-case-lemma1-1)
                   )
             :in-theory (enable aref2 default header)
             ))
    )


  (encapsulate
    ()

    (local
     (defthmd acl2-nump-rot-ind
       (implies (and (not (atom w))
                     (implies (and (acl2-numberp x)
                                   (symbolp name)
                                   (weak-wordp (cdr w)))
                              (and (acl2-numberp (aref2 name (m-* (rotation (cdr w) x) (point-p)) 0 0))
                                   (acl2-numberp (aref2 name (m-* (rotation (cdr w) x) (point-p)) 1 0))
                                   (acl2-numberp (aref2 name (m-* (rotation (cdr w) x) (point-p)) 2 0)))))
                (implies (and (acl2-numberp x) (weak-wordp w) (symbolp name))
                         (and (acl2-numberp (aref2 name (m-* (rotation w x) (point-p)) 0 0))
                              (acl2-numberp (aref2 name (m-* (rotation w x) (point-p)) 1 0))
                              (acl2-numberp (aref2 name (m-* (rotation w x) (point-p)) 2 0)))))
       :hints (("goal"
                :use (
                      (:instance m-*-rotation-point-dim (w (cdr w)) (name name))
                      (:instance rotation-= (w w))
                      (:instance associativity-of-m-*
                                 (m1 (a-rotation x))
                                 (m2 (rotation (cdr w) x))
                                 (m3 (point-p)))
                      (:instance associativity-of-m-*
                                 (m1 (a-inv-rotation x))
                                 (m2 (rotation (cdr w) x))
                                 (m3 (point-p)))
                      (:instance associativity-of-m-*
                                 (m1 (b-rotation x))
                                 (m2 (rotation (cdr w) x))
                                 (m3 (point-p)))
                      (:instance associativity-of-m-*
                                 (m1 (b-inv-rotation x))
                                 (m2 (rotation (cdr w) x))
                                 (m3 (point-p)))

                      (:instance rotation-values-ind-case-lemma1
                                 (m1 (m-* (rotation (cdr w) x) (point-p)))
                                 (name name)
                                 (x x)
                                 )
                      )
                :do-not-induct t
                ))
       )
     )

    (defthmd acl2-nump-rot
      (implies (and (acl2-numberp x)
                    (symbolp name)
                    (weak-wordp w))
               (and (acl2-numberp (aref2 name (m-* (rotation w x) (point-p)) 0 0))
                    (acl2-numberp (aref2 name (m-* (rotation w x) (point-p)) 1 0))
                    (acl2-numberp (aref2 name (m-* (rotation w x) (point-p)) 2 0))))

      :hints (("subgoal *1/5"
               :use (:instance acl2-nump-rot-ind)
               )
              ("subgoal *1/4"
               :use (:instance acl2-nump-rot-ind)
               )
              ("subgoal *1/3"
               :use (:instance acl2-nump-rot-ind)
               )
              ("subgoal *1/2"
               :use (:instance acl2-nump-rot-ind)
               )
              ("subgoal *1/1"
               :in-theory (enable weak-wordp rotation aref2)
               )

              )
      )
    )

  (encapsulate
    ()

    (local
     (defthmd lemma-0-1
       (implies (integerp n)
                (equal (* (expt 3 (- n 1)) 3) (expt 3 n)))
       )
     )

    (local
     (defthmd lemma-0-2
       (implies (integerp x)
                (integerp (* x 3)))
       )
     )

    (local
     (defthmd lemma-0
       (implies (and (acl2-numberp a)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* (/ a x) (expt 3 (- n 1)))))
                (integerp (* (/ a x) (expt 3 n)))
                )

       :hints (("goal"
                :use ((:instance lemma-0-1)
                      (:instance lemma-0-2 (x (* (/ a x) (expt 3 (- n 1)))))
                      )
                ))
       )
     )

    (local
     (defthmd lemma-1-1
       (implies (integerp n)
                (and (equal (expt 3 n) (* (expt 3 (- n 1)) 3))
                     (equal (/ (expt 3 n) 3) (expt 3 (- n 1))))
                )
       )
     )

    (local
     (defthmd lemma-1-2
       (implies (integerp x)
                (and (integerp (* x 4))
                     (integerp (* 4 x))
                     (integerp (* x -4))
                     (integerp (- x))))
       )
     )

    (local
     (defthmd lemma-1-3
       (implies (and (integerp x)
                     (integerp y))
                (and (integerp (+ x y))
                     (integerp (- x y))))
       )
     )

    (local
     (defthmd sqrt-2-lemmas
       (equal (acl2-sqrt 2) (/ 2 (acl2-sqrt 2)))
       :hints (("goal"
                :use (:instance sqrt-* (x 2) (y 2))
                ))
       )
     )

    (local
     (defthmd lemma-1-4
       (implies (and (integerp n)
                     (acl2-numberp b)
                     (acl2-numberp c)
                     )
                (equal (* (/ (- b (* 2 x c)) 3) (expt 3 n))
                       (- (* b (expt 3 (- n 1))) (* 2 x c (expt 3 (- n 1)))))
                )
       :hints (("goal"
                :use (:instance lemma-1-1)
                ))
       )
     )

    (local
     (defthmd lemma-1-5
       (implies (and (integerp n)
                     (acl2-numberp c)
                     (equal x (acl2-sqrt 2))
                     )
                (equal (* 2 x c (expt 3 (- n 1)))
                       (* 4 (/ c x) (expt 3 (- n 1))))
                )
       :hints (("goal"
                :use
                (
                 (:instance sqrt-* (x 2) (y 2))
                 (:instance sqrt-4)
                 (:instance sqrt-2-lemmas)
                 )
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd lemma-1
       (implies (and (acl2-numberp b)
                     (acl2-numberp c)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* b (expt 3 (- n 1))))
                     (integerp (* (/ c x) (expt 3 (- n 1)))))
                (integerp (* (/ (- b (* 2 x c)) 3) (expt 3 n)))
                )

       :hints (("goal"
                :use (
                      (:instance lemma-1-2 (x (* (/ c x) (expt 3 (- n 1)))))
                      (:instance lemma-1-3
                                 (x (* b (expt 3 (- n 1))))
                                 (y (* 4 (/ c x) (expt 3 (- n 1)))))
                      (:instance lemma-1-4)
                      (:instance lemma-1-5)
                      )
                :in-theory nil
                ))
       )
     )

    (local
     (defthmd lemma-2-1
       (implies (and (acl2-numberp b)
                     (acl2-numberp c)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0))
                (equal (* (/ (/ (+ (* 2 x b) c) 3) x) (expt 3 n))
                       (+ (* 2 b (expt 3 (- n 1))) (* (/ c x) (expt 3 (- n 1))))
                       )
                )
       :hints (("goal"
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd lemma-2
       (implies (and (acl2-numberp b)
                     (acl2-numberp c)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* b (expt 3 (- n 1))))
                     (integerp (* (/ c x) (expt 3 (- n 1)))))
                (integerp (* (/ (/ (+ (* 2 x b) c) 3) x) (expt 3 n)))
                )
       :hints (("goal"
                :use ((:instance lemma-2-1))
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd lemma-3-1
       (implies (and (integerp n)
                     (acl2-numberp b)
                     (acl2-numberp c)
                     )
                (equal (* (/ (+ b (* 2 x c)) 3) (expt 3 n))
                       (+ (* b (expt 3 (- n 1))) (* 2 x c (expt 3 (- n 1)))))
                )
       :hints (("goal"
                :use (:instance lemma-1-1)
                ))
       )
     )

    (local
     (defthmd lemma-3
       (implies (and (acl2-numberp b)
                     (acl2-numberp c)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* b (expt 3 (- n 1))))
                     (integerp (* (/ c x) (expt 3 (- n 1)))))
                (integerp (* (/ (+ b (* 2 x c)) 3) (expt 3 n)))
                )
       :hints (("goal"
                :use (
                      (:instance lemma-1-2 (x (* (/ c x) (expt 3 (- n 1)))))
                      (:instance lemma-1-3
                                 (x (* b (expt 3 (- n 1))))
                                 (y (* 4 (/ c x) (expt 3 (- n 1)))))
                      (:instance lemma-3-1)
                      (:instance lemma-1-5)
                      )
                :in-theory nil
                ))
       )
     )

    (local
     (defthmd lemma-4-1
       (implies (and (acl2-numberp b)
                     (acl2-numberp c)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0))
                (equal (* (/ (/ (- c (* 2 x b)) 3) x) (expt 3 n))
                       (- (* (/ c x) (expt 3 (- n 1))) (* 2 b (expt 3 (- n 1))))
                       )
                )
       :hints (("goal"
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd lemma-4
       (implies (and (acl2-numberp b)
                     (acl2-numberp c)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* b (expt 3 (- n 1))))
                     (integerp (* (/ c x) (expt 3 (- n 1)))))
                (integerp (* (/ (/ (- c (* 2 x b)) 3) x) (expt 3 n)))
                )
       :hints (("goal"
                :use (
                      (:instance lemma-4-1)
                      )
                ))
       )
     )

    (local
     (defthmd lemma-5-1
       (implies (and (acl2-numberp a)
                     (acl2-numberp b)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0))
                (equal (* (/ (/ (- a (* 2 x b)) 3) x) (expt 3 n))
                       (- (* (/ a x) (expt 3 (- n 1))) (* 2 b (expt 3 (- n 1))))
                       )
                )
       :hints (("goal"
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd lemma-5
       (implies (and (acl2-numberp a)
                     (acl2-numberp b)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* (/ a x) (expt 3 (- n 1))))
                     (integerp (* b (expt 3 (- n 1)))))
                (integerp (* (/ (/ (- a (* 2 x b)) 3) x) (expt 3 n)))
                )
       :hints (("goal"
                :use (
                      (:instance lemma-5-1)
                      )
                ))
       )
     )

    (local
     (defthmd lemma-6-1
       (implies (and (integerp n)
                     (acl2-numberp b)
                     (acl2-numberp a)
                     )
                (equal (* (/ (+ b (* 2 x a)) 3) (expt 3 n))
                       (+ (* b (expt 3 (- n 1))) (* 2 x a (expt 3 (- n 1)))))
                )
       :hints (("goal"
                :use (:instance lemma-1-1)
                ))
       )
     )

    (local
     (defthmd lemma-6
       (implies (and (acl2-numberp a)
                     (acl2-numberp b)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* (/ a x) (expt 3 (- n 1))))
                     (integerp (* b (expt 3 (- n 1)))))
                (integerp (* (/ (+ b (* 2 x a)) 3) (expt 3 n)))
                )
       :hints (("goal"
                :use (
                      (:instance lemma-1-2 (x (* (/ a x) (expt 3 (- n 1)))))
                      (:instance lemma-1-3
                                 (x (* b (expt 3 (- n 1))))
                                 (y (* 4 (/ a x) (expt 3 (- n 1)))))
                      (:instance lemma-6-1)
                      (:instance lemma-1-5 (c a))
                      )
                :in-theory nil
                ))
       )
     )

    (local
     (defthmd lemma-7
       (implies (and (acl2-numberp c)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* (/ c x) (expt 3 (- n 1)))))
                (integerp (* (/ c x) (expt 3 n)))
                )
       :hints (("goal"
                :use ((:instance lemma-1-1)
                      (:instance lemma-0-2 (x (* (/ c x) (expt 3 (- n 1)))))
                      )
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd lemma-8-1
       (implies (and (acl2-numberp b)
                     (acl2-numberp a)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0))
                (equal (* (/ (/ (+ a (* 2 x b)) 3) x) (expt 3 n))
                       (+ (* (/ a x) (expt 3 (- n 1))) (* 2 b (expt 3 (- n 1))))
                       )
                )
       :hints (("goal"
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd lemma-8
       (implies (and (acl2-numberp a)
                     (acl2-numberp b)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* (/ a x) (expt 3 (- n 1))))
                     (integerp (* b (expt 3 (- n 1)))))
                (integerp (* (/ (/ (+ a (* 2 x b)) 3) x) (expt 3 n)))
                )
       :hints (("goal"
                :use (
                      (:instance lemma-8-1)
                      )
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd lemma-9
       (implies (and (acl2-numberp a)
                     (acl2-numberp b)
                     (equal x (acl2-sqrt 2))
                     (integerp n)
                     (>= n 0)
                     (integerp (* (/ a x) (expt 3 (- n 1))))
                     (integerp (* b (expt 3 (- n 1)))))
                (integerp (* (/ (- b (* 2 x a)) 3) (expt 3 n)))
                )
       :hints (("goal"
                :use (:instance lemma-1 (b b) (c a))
                ))
       )
     )

    (defthmd lemma-int
      (implies (and (acl2-numberp a)
                    (acl2-numberp b)
                    (acl2-numberp c)
                    (equal x (acl2-sqrt 2))
                    (integerp n)
                    (>= n 0)
                    (integerp (* (/ a x) (expt 3 (- n 1))))
                    (integerp (* b (expt 3 (- n 1))))
                    (integerp (* (/ c x) (expt 3 (- n 1))))
                    )
               (and (integerp (* (/ a x) (expt 3 n)))
                    (integerp (* (/ (- b (* 2 x c)) 3) (expt 3 n)))
                    (integerp (* (/ (/ (+ (* 2 x b) c) 3) x) (expt 3 n)))
                    (integerp (* (/ (+ b (* 2 x c)) 3) (expt 3 n)))
                    (integerp (* (/ (/ (- c (* 2 x b)) 3) x) (expt 3 n)))
                    (integerp (* (/ (/ (- a (* 2 x b)) 3) x) (expt 3 n)))
                    (integerp (* (/ (+ b (* 2 x a)) 3) (expt 3 n)))
                    (integerp (* (/ c x) (expt 3 n)))
                    (integerp (* (/ (/ (+ a (* 2 x b)) 3) x) (expt 3 n)))
                    (integerp (* (/ (- b (* 2 x a)) 3) (expt 3 n)))
                    ))
      :hints (("goal"
               :use ((:instance lemma-0)
                     (:instance lemma-1)
                     (:instance lemma-2)
                     (:instance lemma-3)
                     (:instance lemma-4)
                     (:instance lemma-5)
                     (:instance lemma-6)
                     (:instance lemma-7)
                     (:instance lemma-8)
                     (:instance lemma-9)
                     )
               :in-theory nil
               ))
      )
    )

  (defthmd sqrt-2-lemmas
    (and (acl2-numberp (acl2-sqrt 2))
         (i-limited (acl2-sqrt 2))
         (realp (acl2-sqrt 2))
         (equal (* (acl2-sqrt 2) (acl2-sqrt 2)) 2)
         (equal (/ 2 (acl2-sqrt 2)) (acl2-sqrt 2))
         (equal (/ 4 (acl2-sqrt 2)) (* 2 (acl2-sqrt 2)))
         (equal (* 4 (/ (acl2-sqrt 2))) (* 2 (acl2-sqrt 2)))
         (> (acl2-sqrt 2) 1)
         (not (equal (acl2-sqrt 2) 0)))
    :hints (("goal"
             :use ((:instance sqrt-* (x 2) (y 2))

                   )
             :in-theory (disable acl2-sqrt)
             ))
    )

  (defthmd funs-lemmas-2
    (implies (equal x (acl2-sqrt 2))
             (and (m-= (m-* (a-rotation x) (a-inv-rotation x)) (id-rotation))
                  (m-= (m-* (a-inv-rotation x) (a-rotation x)) (id-rotation))
                  (m-= (m-* (b-rotation x) (b-inv-rotation x)) (id-rotation))
                  (m-= (m-* (b-inv-rotation x) (b-rotation x)) (id-rotation))
                  ))
    :hints (("goal"
             :use (:instance sqrt-2-lemmas)
             :in-theory (e/d
                         (alist2p array2p aset2 aref2 compress2 header
                                  dimensions maximum-length default
                                  matrixp compress21
                                  m-=
                                  m-0
                                  m-1
                                  m-trans
                                  m-unary--
                                  s-*
                                  m-binary-+
                                  m-binary-*
                                  m-/
                                  m-singularp
                                  m-binary-*-row-1
                                  m-=-row-1
                                  m-=-row)
                         (acl2-sqrt))
             )
            )
    )

  (defthmd word-len-lemma
    (implies (weak-wordp w)
             (and (integerp (len w))
                  (>= (len w) 0)
                  (if (consp w)
                      (and (equal (- (len w) 1) (len (cdr w)))
                           (equal (len (cdr w)) (- (len w) 1)))
                    0)
                  )
             )
    )

  (encapsulate
    ()

    (local
     (defthm rotation-values-ind-case
       (implies
        (and (consp w)
             (implies (and (weak-wordp (cdr w))
                           (equal x (acl2-sqrt 2)))
                      (and (integerp (int-point (m-* (rotation (cdr w) x) (point-p))
                                                0 0 (len (cdr w))
                                                x))
                           (integerp (int-point (m-* (rotation (cdr w) x) (point-p))
                                                1 0 (len (cdr w))
                                                x))
                           (integerp (int-point (m-* (rotation (cdr w) x) (point-p))
                                                2 0 (len (cdr w))
                                                x)))))
        (implies (and (weak-wordp w)
                      (equal x (acl2-sqrt 2)))
                 (and (integerp (int-point (m-* (rotation w x) (point-p))
                                           0 0 (len w)
                                           x))
                      (integerp (int-point (m-* (rotation w x) (point-p))
                                           1 0 (len w)
                                           x))
                      (integerp (int-point (m-* (rotation w x) (point-p))
                                           2 0 (len w)
                                           x)))))
       :hints (("goal"
                :cases ((equal (car w) (wa))
                        (equal (car w) (wa-inv))
                        (equal (car w) (wb))
                        (equal (car w) (wb-inv))
                        )
                :use (
                      (:instance word-len-lemma (w w))
                      (:instance sqrt-2-lemmas)
                      (:instance weak-word-cdr (x w))
                      (:instance rotation-= (w w) (x x))
                      (:instance associativity-of-m-*
                                 (m1 (a-inv-rotation x))
                                 (m2 (rotation (cdr w) x))
                                 (m3 (point-p)))
                      (:instance associativity-of-m-*
                                 (m1 (b-rotation x))
                                 (m2 (rotation (cdr w) x))
                                 (m3 (point-p)))
                      (:instance associativity-of-m-*
                                 (m1 (b-inv-rotation x))
                                 (m2 (rotation (cdr w) x))
                                 (m3 (point-p)))
                      (:instance associativity-of-m-*
                                 (m1 (a-rotation x))
                                 (m2 (rotation (cdr w) x))
                                 (m3 (point-p)))
                      (:instance word-len-lemma (w w))
                      (:instance weak-word-cdr (x w))
                      (:instance acl2-nump-rot (x x) (name '$arg1) (w (cdr w)))
                      (:instance m-*-rotation-point-dim (w (cdr w)) (name '$arg1))
                      (:instance rotation-values-ind-case-lemma1
                                 (name '$arg1)
                                 (x x)
                                 (m1 (m-* (rotation (cdr w) x) (point-p)))
                                 )
                      (:instance lemma-int
                                 (x x)
                                 (n (len w))
                                 (a (aref2 '$arg1 (m-* (rotation (cdr w) x) (point-p)) 0 0))
                                 (b (aref2 '$arg1 (m-* (rotation (cdr w) x) (point-p)) 1 0))
                                 (c (aref2 '$arg1 (m-* (rotation (cdr w) x) (point-p)) 2 0)))
                      (:instance int-point
                                 (a (m-* (rotation w (acl2-sqrt 2))
                                         (point-p)))
                                 (i 0)
                                 (j 0)
                                 (n (len w))
                                 (x x))
                      (:instance int-point
                                 (a (m-* (rotation w (acl2-sqrt 2))
                                         (point-p)))
                                 (i 1)
                                 (j 0)
                                 (n (len w))
                                 (x x))
                      (:instance int-point
                                 (a (m-* (rotation w (acl2-sqrt 2))
                                         (point-p)))
                                 (i 2)
                                 (j 0)
                                 (n (len w))
                                 (x x))
                      (:instance int-point
                                 (a (m-* (rotation (cdr w) (acl2-sqrt 2))
                                         (point-p)))
                                 (i 0)
                                 (j 0)
                                 (n (len (cdr w)))
                                 (x x))
                      (:instance int-point
                                 (a (m-* (rotation (cdr w) (acl2-sqrt 2))
                                         (point-p)))
                                 (i 1)
                                 (j 0)
                                 (n (len (cdr w)))
                                 (x x))
                      (:instance int-point
                                 (a (m-* (rotation (cdr w) (acl2-sqrt 2))
                                         (point-p)))
                                 (i 2)
                                 (j 0)
                                 (n (len (cdr w)))
                                 (x x))
                      )
                :in-theory nil
                :do-not-induct t
                )
               )
       )
     )

    (defthmd rotation-values
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (and (integerp (int-point (m-* (rotation w x) (point-p)) 0 0 (len w) x))
                    (integerp (int-point (m-* (rotation w x) (point-p)) 1 0 (len w) x))
                    (integerp (int-point (m-* (rotation w x) (point-p)) 2 0 (len w) x))
                    )
               )
      :hints (("subgoal *1/1"
               :use ((:instance rotation-values-ind-case))
               :in-theory (disable acl2-sqrt)
               ))
      )
    )

  (defun n-f(w x)
    (cons (int-point (m-* (rotation w x) (point-p)) 0 0 (len w) (acl2-sqrt 2))
          (cons (int-point (m-* (rotation w x) (point-p)) 1 0 (len w) (acl2-sqrt 2))
                (cons (int-point (m-* (rotation w x) (point-p)) 2 0 (len w) (acl2-sqrt 2)) nil)))
    )

  (encapsulate
    ()

    (local
     (defthmd len-wa-inv-lemma
       (implies (weak-wordp w)
                (and (equal (len (cons (wa-inv) w)) (+ (len w) 1))
                     (integerp (len w)))
                )
       )
     )

    (local
     (defthmd n-f-a-inv-r-lemma
       (implies (weak-wordp w)
                (equal (rotation (cons (wa-inv) w) x)
                       (m-* (a-inv-rotation x) (rotation w x))))
       )
     )

    (local
     (defthmd expt-lemma
       (implies (integerp n)
                (equal (expt 3 (+ n 1)) (* (expt 3 n) 3)))
       )
     )

    (local
     (defthmd wa-inv-sub4-lemma
       (implies (equal (+ (* 1/3 y) (* -2/3 (acl2-sqrt 2) x))
                       z)
                (equal (+ (* 2 x) (* 3 (/ (acl2-sqrt 2)) z))
                       (* (/ (acl2-sqrt 2)) y)))
       :hints (("goal"
                :use (:instance sqrt-2-lemmas)

                ))
       )
     )

    (local
     (defthmd wa-inv-sub2-lemma
       (implies (equal (+ (* 1/3 b) (* 2/3 (acl2-sqrt 2) c))
                       z)
                (equal (* 3 z)
                       (+ b (* 4 (/ (acl2-sqrt 2)) c))))
       :hints (("goal"
                :use ((:instance sqrt-2-lemmas))
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (defthmd n-f-a-inv-r
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (equal (n-f (cons (wa-inv) w) x) (cons (* 3 (car (n-f w x))) (cons (+ (car (cdr (n-f w x))) (* 4 (car (cdr (cdr (n-f w x)))))) (cons (- (car (cdr (cdr (n-f w x)))) (* 2 (car (cdr (n-f w x))))) nil)))))
      :hints (("goal"
               :use ((:instance m-*-rotation-point-dim (w w) (x x) (name '$arg1))
                     (:instance rotation-values-ind-case-lemma1 (name '$arg1) (m1 (m-* (rotation w x) (point-p))))
                     (:instance acl2-nump-rot (w w) (name '$arg1) (x x))
                     (:instance sqrt-2-lemmas)
                     (:instance len-wa-inv-lemma (w w))
                     (:instance n-f-a-inv-r-lemma (w w) (x (acl2-sqrt 2)))
                     (:instance n-f (w w) (x x))
                     (:instance n-f (w (cons (wa-inv) w)) (x x))
                     (:instance associativity-of-m-*
                                (m1 (a-inv-rotation x))
                                (m2 (rotation w x))
                                (m3 (point-p)))
                     (:instance expt-lemma (n (len w)))
                     )
               :in-theory (disable aref2 rotation a-rotation b-rotation m-* a-inv-rotation b-inv-rotation point-p acl2-sqrt rotation weak-wordp)
               :do-not-induct t
               )
              ("subgoal 4"
               :use (:instance wa-inv-sub4-lemma
                               (x (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         1 0))
                               (y (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         2 0))
                               (z (aref2 '$arg1
                                         (m-* (rotation (cons #\b w) (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         2 0))
                               )
               )
              ("subgoal 2"
               :use (:instance wa-inv-sub2-lemma
                               (z (aref2 '$arg1
                                         (m-* (rotation (cons #\b w) (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         1 0))
                               (b (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         1 0))
                               (c (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         2 0)
                                  )
                               )
               )
              )
      )
    )

  (encapsulate
    ()

    (local
     (defthmd len-wb-lemma
       (implies (weak-wordp w)
                (and (equal (len (cons (wb) w)) (+ (len w) 1))
                     (integerp (len w)))
                )
       )
     )

    (local
     (defthmd n-f-b-r-lemma
       (implies (weak-wordp w)
                (equal (rotation (cons (wb) w) x)
                       (m-* (b-rotation x) (rotation w x))))
       )
     )

    (local
     (defthmd expt-lemma
       (implies (integerp n)
                (equal (expt 3 (+ n 1)) (* (expt 3 n) 3)))
       )
     )

    (local
     (defthmd wb-sub6-lemma
       (implies (equal (+ (* 1/3 a) (* -2/3 (acl2-sqrt 2) b)) x)
                (equal (+ (* 2 b) (* 3 (/ (acl2-sqrt 2)) x))
                       (* (/ (acl2-sqrt 2)) a)))
       :hints (("goal"
                :use (:instance sqrt-2-lemmas)
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd wb-sub2-lemma
       (implies (equal (+ (* 1/3 b) (* 2/3 (acl2-sqrt 2) a))
                       y)
                (equal (* 3 y)
                       (+ b (* 4 (/ (acl2-sqrt 2)) a))))
       :hints (("goal"
                :use ((:instance sqrt-2-lemmas))
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (defthmd n-f-b-r
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (equal (n-f (cons (wb) w) x) (cons (- (car (n-f w x)) (* 2 (car (cdr (n-f w x)))))
                                                  (cons (+ (* 4 (car (n-f w x))) (car (cdr (n-f w x))))
                                                        (cons (* 3 (car (cdr (cdr (n-f w x))))) nil)))))
      :hints (("goal"
               :use ((:instance m-*-rotation-point-dim (w w) (x x) (name '$arg1))
                     (:instance rotation-values-ind-case-lemma1 (name '$arg1) (m1 (m-* (rotation w x) (point-p))))
                     (:instance acl2-nump-rot (w w) (name '$arg1) (x x))
                     (:instance sqrt-2-lemmas)
                     (:instance len-wb-lemma (w w))
                     (:instance n-f-b-r-lemma (w w) (x (acl2-sqrt 2)))
                     (:instance n-f (w w) (x x))
                     (:instance n-f (w (cons (wb) w)) (x x))
                     (:instance associativity-of-m-*
                                (m1 (b-rotation x))
                                (m2 (rotation w x))
                                (m3 (point-p)))
                     (:instance expt-lemma (n (len w)))
                     )
               :in-theory (disable aref2 rotation a-rotation b-rotation m-* a-inv-rotation b-inv-rotation point-p acl2-sqrt rotation weak-wordp)
               :do-not-induct t
               )
              ("subgoal 6"
               :use (:instance wb-sub6-lemma
                               (x (aref2 '$arg1
                                         (m-* (b-rotation (acl2-sqrt 2))
                                              (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         0 0))
                               (a (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         0 0))
                               (b (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         1 0))
                               )
               )
              ("subgoal 2"
               :use (:instance wb-sub2-lemma
                               (y (aref2 '$arg1
                                         (m-* (rotation (cons #\c w) (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         1 0))
                               (b (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         1 0))
                               (a (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         0 0))
                               )
               )
              )
      )
    )

  (encapsulate
    ()

    (local
     (defthmd len-wb-inv-lemma
       (implies (weak-wordp w)
                (and (equal (len (cons (wb-inv) w)) (+ (len w) 1))
                     (integerp (len w)))
                )
       )
     )

    (local
     (defthmd n-f-b-inv-r-lemma
       (implies (weak-wordp w)
                (equal (rotation (cons (wb-inv) w) x)
                       (m-* (b-inv-rotation x) (rotation w x))))
       )
     )

    (local
     (defthmd expt-lemma
       (implies (integerp n)
                (equal (expt 3 (+ n 1)) (* (expt 3 n) 3)))
       )
     )

    (local
     (defthmd wb-inv-sub2-lemma1-1
       (equal (* 4 (/ (acl2-sqrt 2)) a)
              (* 2 (acl2-sqrt 2) a))
       :hints (("goal"
                :use ((:instance sqrt-2-lemmas))
                :in-theory (disable acl2-sqrt)
                :do-not-induct t
                ))
       )
     )

    (local
     (defthmd wb-inv-sub2-lemma1-2
       (equal (* 3
                 (+ (* 1/3 b)
                    (- (* 2/3 x a))))
              (- b (* 2 x a))))
     )

    (local
     (defthmd wb-inv-sub2-lemma1
       (implies (equal (+ (* 1/3 b) (* -2/3 (acl2-sqrt 2) a)) y)
                (equal (- (+ (* 3 y) (* 4 (/ (acl2-sqrt 2)) a)) b)
                       0))
       :hints (("goal"
                :use ((:instance sqrt-2-lemmas)
                      (:instance wb-inv-sub2-lemma1-1 (a a))
                      (:instance wb-inv-sub2-lemma1-2 (b b) (a a) (x (acl2-sqrt 2))))
                :in-theory (disable acl2-sqrt)
                :do-not-induct t
                ))
       )
     )

    (local
     (defthmd wb-inv-sub2-lemma
       (implies (and (acl2-numberp b)
                     (equal (+ (* 1/3 b) (* -2/3 (acl2-sqrt 2) a)) y))
                (equal (+ (* 3 y) (* 4 (/ (acl2-sqrt 2)) a))
                       b))
       :hints (("goal"
                :use (
                      (:instance wb-inv-sub2-lemma1))
                :in-theory (disable acl2-sqrt)
                :do-not-induct t
                ))
       )
     )

    (defthmd n-f-b-inv-r
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (equal (n-f (cons (wb-inv) w) x) (cons (+ (car (n-f w x)) (* 2 (car (cdr (n-f w x)))))
                                                      (cons (- (car (cdr (n-f w x))) (* 4 (car (n-f w x))))
                                                            (cons (* 3 (car (cdr (cdr (n-f w x))))) nil)))))
      :hints (("goal"
               :use ((:instance m-*-rotation-point-dim (w w) (x x) (name '$arg1))
                     (:instance rotation-values-ind-case-lemma1 (name '$arg1) (m1 (m-* (rotation w x) (point-p))))
                     (:instance acl2-nump-rot (w w) (name '$arg1) (x x))
                     (:instance sqrt-2-lemmas)
                     (:instance len-wb-inv-lemma (w w))
                     (:instance n-f-b-inv-r-lemma (w w) (x (acl2-sqrt 2)))
                     (:instance n-f (w w) (x x))
                     (:instance n-f (w (cons (wb-inv) w)) (x x))
                     (:instance associativity-of-m-*
                                (m1 (b-inv-rotation x))
                                (m2 (rotation w x))
                                (m3 (point-p)))
                     (:instance expt-lemma (n (len w)))
                     )
               :in-theory (disable aref2 rotation a-rotation b-rotation m-* a-inv-rotation b-inv-rotation point-p acl2-sqrt rotation weak-wordp)
               :do-not-induct t
               )
              ("subgoal 2"
               :use (:instance wb-inv-sub2-lemma
                               (y (aref2 '$arg1
                                         (m-* (rotation (cons #\d w) (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         1 0))
                               (a (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         0 0))
                               (b (aref2 '$arg1
                                         (m-* (rotation w (acl2-sqrt 2))
                                              '((:header :dimensions (3 1)
                                                         :maximum-length 15)
                                                ((0 . 0) . 0)
                                                ((1 . 0) . 1)
                                                ((2 . 0) . 0)))
                                         1 0))
                               )
               )
              )
      )
    )


  (encapsulate
    ()

    (local
     (defthmd len-lemma
       (implies (weak-wordp w)
                (and (equal (len (cons (wa) w)) (+ (len w) 1))
                     (integerp (len w)))
                )
       )
     )

    (local
     (defthmd n-f-a-r-lemma
       (implies (weak-wordp w)
                (equal (rotation (cons (wa) w) x)
                       (m-* (a-rotation x) (rotation w x))))
       )
     )

    (local
     (defthmd expt-lemma
       (implies (integerp n)
                (equal (expt 3 (+ n 1)) (* (expt 3 n) 3)))
       )
     )

    (local
     (defthmd sub4-lemma0
       (implies
        (equal (+ (* 1/3
                     (aref2 '$arg1
                            (m-* (rotation w (acl2-sqrt 2))
                                 '((:header :dimensions (3 1)
                                            :maximum-length 15)
                                   ((0 . 0) . 0)
                                   ((1 . 0) . 1)
                                   ((2 . 0) . 0)))
                            2 0))
                  (* 2/3 (acl2-sqrt 2)
                     (aref2 '$arg1
                            (m-* (rotation w (acl2-sqrt 2))
                                 '((:header :dimensions (3 1)
                                            :maximum-length 15)
                                   ((0 . 0) . 0)
                                   ((1 . 0) . 1)
                                   ((2 . 0) . 0)))
                            1 0)))
               (aref2 '$arg1
                      (m-* (a-rotation (acl2-sqrt 2))
                           (rotation w (acl2-sqrt 2))
                           '((:header :dimensions (3 1)
                                      :maximum-length 15)
                             ((0 . 0) . 0)
                             ((1 . 0) . 1)
                             ((2 . 0) . 0)))
                      2 0))
        (equal
         (aref2 '$arg1
                (m-* (a-rotation (acl2-sqrt 2))
                     (rotation w (acl2-sqrt 2))
                     '((:header :dimensions (3 1)
                                :maximum-length 15)
                       ((0 . 0) . 0)
                       ((1 . 0) . 1)
                       ((2 . 0) . 0)))
                2 0)
         (+
          (* 2/3 (acl2-sqrt 2)
             (aref2 '$arg1
                    (m-* (rotation w (acl2-sqrt 2))
                         '((:header :dimensions (3 1)
                                    :maximum-length 15)
                           ((0 . 0) . 0)
                           ((1 . 0) . 1)
                           ((2 . 0) . 0)))
                    1 0))
          (* 1/3
             (aref2 '$arg1
                    (m-* (rotation w (acl2-sqrt 2))
                         '((:header :dimensions (3 1)
                                    :maximum-length 15)
                           ((0 . 0) . 0)
                           ((1 . 0) . 1)
                           ((2 . 0) . 0)))
                    2 0)))
         )
        )
       )
     )

    (local
     (defthmd sub4-lemma1
       (equal
        (aref2 '$arg1
               (m-* (rotation (cons #\a w) (acl2-sqrt 2))
                    '((:header :dimensions (3 1)
                               :maximum-length 15)
                      ((0 . 0) . 0)
                      ((1 . 0) . 1)
                      ((2 . 0) . 0)))
               2 0)
        (aref2 '$arg1
               (m-* (a-rotation (acl2-sqrt 2))
                    (rotation w (acl2-sqrt 2))
                    '((:header :dimensions (3 1)
                               :maximum-length 15)
                      ((0 . 0) . 0)
                      ((1 . 0) . 1)
                      ((2 . 0) . 0)))
               2 0)
        )
       )
     )

    (local
     (defthmd sub4-lemma2
       (implies
        (equal (+ (* 1/3
                     (aref2 '$arg1
                            (m-* (rotation w (acl2-sqrt 2))
                                 '((:header :dimensions (3 1)
                                            :maximum-length 15)
                                   ((0 . 0) . 0)
                                   ((1 . 0) . 1)
                                   ((2 . 0) . 0)))
                            2 0))
                  (* 2/3 (acl2-sqrt 2)
                     (aref2 '$arg1
                            (m-* (rotation w (acl2-sqrt 2))
                                 '((:header :dimensions (3 1)
                                            :maximum-length 15)
                                   ((0 . 0) . 0)
                                   ((1 . 0) . 1)
                                   ((2 . 0) . 0)))
                            1 0)))
               (aref2 '$arg1
                      (m-* (a-rotation (acl2-sqrt 2))
                           (rotation w (acl2-sqrt 2))
                           '((:header :dimensions (3 1)
                                      :maximum-length 15)
                             ((0 . 0) . 0)
                             ((1 . 0) . 1)
                             ((2 . 0) . 0)))
                      2 0))
        (equal (* 3 (/ (acl2-sqrt 2))
                  (aref2 '$arg1
                         (m-* (rotation (cons #\a w) (acl2-sqrt 2))
                              '((:header :dimensions (3 1)
                                         :maximum-length 15)
                                ((0 . 0) . 0)
                                ((1 . 0) . 1)
                                ((2 . 0) . 0)))
                         2 0))
               (+ (* 2
                     (aref2 '$arg1
                            (m-* (rotation w (acl2-sqrt 2))
                                 '((:header :dimensions (3 1)
                                            :maximum-length 15)
                                   ((0 . 0) . 0)
                                   ((1 . 0) . 1)
                                   ((2 . 0) . 0)))
                            1 0))
                  (* (/ (acl2-sqrt 2))
                     (aref2 '$arg1
                            (m-* (rotation w (acl2-sqrt 2))
                                 '((:header :dimensions (3 1)
                                            :maximum-length 15)
                                   ((0 . 0) . 0)
                                   ((1 . 0) . 1)
                                   ((2 . 0) . 0)))
                            2 0))))
        )
       :hints (("goal"
                :use (
                      (:instance sub4-lemma0)
                      (:instance sub4-lemma1)
                      )
                :in-theory (disable m-* aref2 acl2-sqrt)
                ))
       )
     )

    (local
     (defthmd sub2-lemma
       (implies (and (acl2-numberp x)
                     (equal (+ (* 1/3 x) (* -2/3 (acl2-sqrt 2) y)) z))
                (equal (+ (* 3 z) (* 4 (/ (acl2-sqrt 2)) y)) x))
       :hints (("goal"
                :use (:instance sqrt-2-lemmas)
                :in-theory (disable acl2-sqrt)
                ))
       )
     )

    (defthmd n-f-a-r
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (equal (n-f (cons (wa) w) x) (cons (* 3 (car (n-f w x))) (cons (- (car (cdr (n-f w x))) (* 4 (car (cdr (cdr (n-f w x)))))) (cons (+ (* 2 (car (cdr (n-f w x)))) (car (cdr (cdr (n-f w x))))) nil)))))
      :hints (("goal"
               :use ((:instance m-*-rotation-point-dim (w w) (x x) (name '$arg1))
                     (:instance rotation-values-ind-case-lemma1 (name '$arg1) (m1 (m-* (rotation w x) (point-p))))
                     (:instance acl2-nump-rot (w w) (name '$arg1) (x x))
                     (:instance sqrt-2-lemmas)
                     (:instance len-lemma (w w))
                     (:instance n-f-a-r-lemma (w w) (x (acl2-sqrt 2)))
                     (:instance n-f (w w) (x x))
                     (:instance n-f (w (cons (wa) w)) (x x))
                     (:instance associativity-of-m-*
                                (m1 (a-rotation x))
                                (m2 (rotation w x))
                                (m3 (point-p)))
                     (:instance expt-lemma (n (len w)))
                     )
               :in-theory (disable aref2 rotation a-rotation b-rotation m-* a-inv-rotation b-inv-rotation point-p acl2-sqrt rotation weak-wordp)
               :do-not-induct t
               )
              ("subgoal 4"
               :use (
                     (:instance sub4-lemma0)
                     (:instance sub4-lemma1)
                     (:instance sub4-lemma2)
                     )
               )

              ("subgoal 2"
               :use (
                     (:instance sub2-lemma
                                (x (aref2 '$arg1
                                          (m-* (rotation w (acl2-sqrt 2))
                                               '((:header :dimensions (3 1)
                                                          :maximum-length 15)
                                                 ((0 . 0) . 0)
                                                 ((1 . 0) . 1)
                                                 ((2 . 0) . 0)))
                                          1 0))
                                (y (aref2 '$arg1
                                          (m-* (rotation w (acl2-sqrt 2))
                                               '((:header :dimensions (3 1)
                                                          :maximum-length 15)
                                                 ((0 . 0) . 0)
                                                 ((1 . 0) . 1)
                                                 ((2 . 0) . 0)))
                                          2 0))
                                (z (aref2 '$arg1
                                          (m-* (a-rotation (acl2-sqrt 2))
                                               (rotation w (acl2-sqrt 2))
                                               '((:header :dimensions (3 1)
                                                          :maximum-length 15)
                                                 ((0 . 0) . 0)
                                                 ((1 . 0) . 1)
                                                 ((2 . 0) . 0)))
                                          1 0))
                                )
                     )
               )
              )
      )
    )

  (encapsulate
    ()
    (local (include-book "workshops/1999/embedded/Exercises/Exercise1-2/Exercise1.2" :dir :system))
    (defthmd mod--frgrp
      (implies
       (and (force (integerp x))
            (force (integerp y))
            (force (integerp z))
            (force (not (equal z 0))))
       (equal (mod (- x y) z)
              (mod (- (mod x z) (mod y z)) z)))
      :hints (("goal" :use (hack-24 hack-25))))

    (defthmd mod--frgrp-1
      (implies
       (and (force (integerp x))
            (force (integerp y))
            (force (integerp z))
            (force (not (equal z 0))))
       (equal
        (mod (- (mod x z) (mod y z)) z)
        (mod (- x y) z)))
      :hints (("goal" :use (mod--frgrp))))

    (defthmd intp-x-y
      (implies (and (integerp x)
                    (integerp y))
               (integerp (mod y x)))
      )

    (defthmd mod-+-frgrp
      (implies
       (and (integerp x)
            (integerp y)
            (integerp z)
            (not (equal z 0)))
       (equal (mod (+ x y) z)
              (mod (+ (mod x z) (mod y z)) z)))
      :hints (("goal"
               :in-theory nil
               :use (:instance mod-+-exp))
              )
      )
    )

  (defun n-mod3 (w x)
    (cons (mod (car (n-f w x)) 3) (cons (mod (car (cdr (n-f w x))) 3) (cons (mod (car (cdr (cdr (n-f w x) )))  3) nil)))
    )

  (defthmd n-mod3-=
    (and  (equal (mod (car (n-f w x)) 3)
                 (car (n-mod3 w x)))
          (equal (mod (cadr (n-f w x)) 3)
                 (cadr (n-mod3 w x)))
          (equal (mod (caddr (n-f w x)) 3)
                 (caddr (n-mod3 w x))))
    :hints (("goal"
             :in-theory (disable mod n-f)
             ))
    )

;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;n(a)
;;;;;;;;;;;;;;;;;;;;;;;;;
  (encapsulate
    ()

    (local
     (defthmd n-mod3-a-r-lemma1-1
       (implies (and (integerp a)
                     (integerp c))
                (equal (mod (+ a (* 3 c))  3)
                       (mod a 3)
                       )
                )
       )
     )

    (local
     (defthmd n-mod3-a-r-lemma1-3
       (equal (- b (* 4 c))
              (- (- b c) (* 3 c)))
       )
     )

    (local
     (defthmd n-mod3-a-r-lemma1-4
       (equal (+  (* 2 b) c)
              (+ (- c b) (* 3 b)))
       )
     )

    (local
     (defthmd n-mod3-a-r-lemma1-5
       (implies (and (integerp b)
                     (integerp c))
                (and (equal (- b (* 4 c))
                            (- (- b c) (* 3 c)))
                     (equal (mod (- b (* 4 c)) 3)
                            (mod (- b  c) 3))
                     (equal (mod (+ (* 2 b) c) 3)
                            (mod (- c b) 3))))
       :hints (("goal"
                :use ((:instance n-mod3-a-r-lemma1-3 (b b) (c c))
                      (:instance n-mod3-a-r-lemma1-1 (a (- b c)) (c (- c)))
                      (:instance n-mod3-a-r-lemma1-4 (b b) (c c))
                      (:instance n-mod3-a-r-lemma1-1 (a (- c b)) (c b))
                      )
                ))
       )
     )

    (local
     (defthmd n-mod3-a-r-lemma1-6
       (implies (and (weak-wordp w)
                     (equal x (acl2-sqrt 2)))
                (and (integerp (car (n-f w x)))
                     (integerp (cadr (n-f w x)))
                     (integerp (caddr (n-f w x)))
                     (equal (car (n-f (cons (wa) w) x)) (* 3 (car (n-f w x))))
                     (equal (cadr (n-f (cons (wa) w) x))
                            (+ (cadr (n-f w x))
                               (- (* 4 (caddr (n-f w x))))))
                     (equal (caddr (n-f (cons (wa) w) x))
                            (+ (* 2 (cadr (n-f w x)))
                               (caddr (n-f w x)))))
                )
       :hints (("goal"
                :use ((:instance rotation-values (w w) (x x))
                      (:instance n-f-a-r (w w) (x x))
                      (:instance n-f (w w) (x x))
                      (:instance n-f (w (cons (wa) w)) (x x)))
                :in-theory (disable int-point acl2-sqrt rotation reducedwordp mod)
                ))
       )
     )

    (defthmd integerp-n-mod3
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (and (integerp (car (n-mod3 w x)))
                    (integerp (cadr (n-mod3 w x)))
                    (integerp (caddr (n-mod3 w x)))
                    )
               )
      :hints (("goal"
               :use ((:instance n-mod3-=)
                     (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
                     (:instance intp-x-y (x 3) (y (car (n-f w x))))
                     (:instance intp-x-y (x 3) (y (car (cdr (n-f w x)))))
                     (:instance intp-x-y (x 3) (y (car (cdr (cdr (n-f w x))))))
                     )
               :in-theory nil
               ))
      )

    (local
     (defthmd n-mod3-a-r-lemma1
       (implies (and (weak-wordp w)
                     (equal x (acl2-sqrt 2)))
                (equal (n-mod3 (cons (wa) w) x)
                       (cons 0 (cons (mod (- (car (cdr (n-f w x)))  (car (cdr (cdr (n-f w x))))) 3)
                                     (cons (mod (- (car (cdr (cdr (n-f w x)))) (car (cdr (n-f w x)))) 3) nil)))

                       )
                )
       :hints (("goal"
                :use (
                      (:instance n-mod3 (w (cons (wa) w)) (x x))
                      (:instance n-mod3-a-r-lemma1-1 (a 0) (c (car (n-f w x))))
                      (:instance n-mod3-a-r-lemma1-5 (b (cadr (n-f w x))) (c (caddr (n-f w x))))
                      (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
                      )
                :in-theory (disable int-point rotation reducedwordp acl2-sqrt n-f mod)
                :do-not-induct t
                )
               )
       )
     )

    (local
     (defthmd n-mod3-a-r-1
       (implies (and (integerp x)
                     (integerp y)
                     (not (equal y 0)))
                (integerp (mod x y)))
       )
     )

    (defthmd n-mod3-a-r
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (equal (n-mod3 (cons (wa) w) x)
                      (cons 0 (cons (mod (- (car (cdr (n-mod3 w x)))  (car (cdr (cdr (n-mod3 w x))))) 3)
                                    (cons (mod (- (car (cdr (cdr (n-mod3 w x)))) (car (cdr (n-mod3 w x)))) 3) nil)))

                      )
               )
      :hints (("goal"
               :use (
                     (:instance n-mod3-a-r-lemma1 (w w) (x x))
                     (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
                     (:instance n-mod3-a-r-1 (x (cadr (n-f w x))) (y 3))
                     (:instance n-mod3-a-r-1 (x (caddr (n-f w x))) (y 3))
                     (:instance mod--frgrp
                                (x (cadr (n-f w x)))
                                (y (caddr (n-f w x)))
                                (z 3))

                     (:instance mod--frgrp
                                (y (cadr (n-f w x)))
                                (x (caddr (n-f w x)))
                                (z 3))
                     (:instance n-mod3-=)

                     )
               :in-theory nil
               :do-not-induct t
               ))

      )
    )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;n(a-inv)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  (encapsulate
    ()

    (local
     (defthmd n-mod3-a-r-lemma1-1
       (implies (and (integerp a)
                     (integerp c))
                (equal (mod (+ a (* 3 c))  3)
                       (mod a 3)
                       )
                )
       )
     )

    (local
     (defthmd n-mod3-a-r-lemma1-3
       (equal (+ b (* 4 c))
              (+ (+ b c) (* 3 c)))
       )
     )

    (local
     (defthmd n-mod3-a-r-lemma1-4
       (equal (- c  (* 2 b))
              (- (+ c b) (* 3 b)))
       )
     )

    (local
     (defthmd n-mod3-a-r-lemma1-5
       (implies (and (integerp b)
                     (integerp c))
                (and (equal (+ b (* 4 c))
                            (+ (+ b c) (* 3 c)))
                     (equal (mod (+ b (* 4 c)) 3)
                            (mod (+ b  c) 3))
                     (equal (mod (- c (* 2 b)) 3)
                            (mod (+ c b) 3))))
       :hints (("goal"
                :use ((:instance n-mod3-a-r-lemma1-3 (b b) (c c))
                      (:instance n-mod3-a-r-lemma1-1 (a (+ b c)) (c c))
                      (:instance n-mod3-a-r-lemma1-4 (b b) (c c))
                      (:instance n-mod3-a-r-lemma1-1 (a (+ c b)) (c (- b)))
                      )
                ))
       )
     )

    (local
     (defthmd n-mod3-a-r-lemma1-6
       (implies (and (weak-wordp w)
                     (equal x (acl2-sqrt 2)))
                (and (integerp (car (n-f w x)))
                     (integerp (cadr (n-f w x)))
                     (integerp (caddr (n-f w x)))
                     (equal (car (n-f (cons (wa-inv) w) x)) (* 3 (car (n-f w x))))
                     (equal (cadr (n-f (cons (wa-inv) w) x))
                            (+ (cadr (n-f w x))
                               (+ (* 4 (caddr (n-f w x))))))
                     (equal (caddr (n-f (cons (wa-inv) w) x))
                            (- (caddr (n-f w x)) (* 2 (cadr (n-f w x))))))

                )
       :hints (("goal"
                :use ((:instance rotation-values (w w) (x x))
                      (:instance n-f-a-inv-r (w w) (x x))
                      (:instance n-f (w w) (x x))
                      (:instance n-f (w (cons (wa-inv) w)) (x x)))
                :in-theory (disable int-point acl2-sqrt rotation reducedwordp mod)
                ))
       )
     )

    (local
     (defthmd n-mod3-a-r-lemma1
       (implies (and (weak-wordp w)
                     (equal x (acl2-sqrt 2)))
                (equal (n-mod3 (cons (wa-inv) w) x)
                       (cons 0 (cons (mod (+ (car (cdr (n-f w x)))  (car (cdr (cdr (n-f w x))))) 3)
                                     (cons (mod (+ (car (cdr (cdr (n-f w x)))) (car (cdr (n-f w x)))) 3) nil)))
                       )
                )
       :hints (("goal"
                :use (
                      (:instance n-mod3 (w (cons (wa-inv) w)) (x x))
                      (:instance n-mod3-a-r-lemma1-1 (a 0) (c (car (n-f w x))))
                      (:instance n-mod3-a-r-lemma1-5 (b (cadr (n-f w x))) (c (caddr (n-f w x))))
                      (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
                      )
                :in-theory (disable int-point rotation reducedwordp acl2-sqrt n-f mod)
                :do-not-induct t
                )
               )
       )
     )

    (local
     (defthmd n-mod3-a-r-1
       (implies (and (integerp x)
                     (integerp y)
                     (not (equal y 0)))
                (integerp (mod x y)))
       )
     )

    (defthmd n-mod3-a-inv-r
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (equal (n-mod3 (cons (wa-inv) w) x)
                      (cons 0 (cons (mod (+ (car (cdr (n-mod3 w x)))  (car (cdr (cdr (n-mod3 w x))))) 3)
                                    (cons (mod (+ (car (cdr (cdr (n-mod3 w x)))) (car (cdr (n-mod3 w x)))) 3) nil)))
                      )
               )
      :hints (("goal"
               :use (
                     (:instance n-mod3-a-r-lemma1 (w w) (x x))
                     (:instance n-mod3-a-r-lemma1-6 (w w) (x x))
                     (:instance n-mod3-a-r-1 (x (cadr (n-f w x))) (y 3))
                     (:instance n-mod3-a-r-1 (x (caddr (n-f w x))) (y 3))
                     (:instance mod-+-frgrp
                                (x (cadr (n-f w x)))
                                (y (caddr (n-f w x)))
                                (z 3))

                     (:instance mod-+-frgrp
                                (y (cadr (n-f w x)))
                                (x (caddr (n-f w x)))
                                (z 3))
                     (:instance n-mod3-=)

                     )
               :in-theory nil
               :do-not-induct t
               ))

      )
    )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;n(b)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  (encapsulate
    ()

    (local
     (defthmd n-mod3-b-r-lemma1-1
       (implies (and (integerp a)
                     (integerp c))
                (equal (mod (+ a (* 3 c))  3)
                       (mod a 3)
                       )
                )
       )
     )

    (local
     (defthmd n-mod3-b-r-lemma1-3
       (equal (+ b (* 4 c))
              (+ (+ b c) (* 3 c)))
       )
     )

    (local
     (defthmd n-mod3-b-r-lemma1-4
       (equal (- c  (* 2 b))
              (- (+ c b) (* 3 b)))
       )
     )

    (local
     (defthmd n-mod3-b-r-lemma1-5
       (implies (and (integerp b)
                     (integerp c))
                (and (equal (+ b (* 4 c))
                            (+ (+ b c) (* 3 c)))
                     (equal (mod (+ b (* 4 c)) 3)
                            (mod (+ b  c) 3))
                     (equal (mod (- c (* 2 b)) 3)
                            (mod (+ c b) 3))))
       :hints (("goal"
                :use ((:instance n-mod3-b-r-lemma1-3 (b b) (c c))
                      (:instance n-mod3-b-r-lemma1-1 (a (+ b c)) (c c))
                      (:instance n-mod3-b-r-lemma1-4 (b b) (c c))
                      (:instance n-mod3-b-r-lemma1-1 (a (+ c b)) (c (- b)))
                      )
                ))
       )
     )

    (local
     (defthmd n-mod3-b-r-lemma1-6
       (implies (and (weak-wordp w)
                     (equal x (acl2-sqrt 2)))
                (and (integerp (car (n-f w x)))
                     (integerp (cadr (n-f w x)))
                     (integerp (caddr (n-f w x)))
                     (equal (car (n-f (cons (wb) w) x)) (- (car (n-f w x)) (* 2 (cadr (n-f w x)))))
                     (equal (cadr (n-f (cons (wb) w) x))
                            (+ (cadr (n-f w x))
                               (+ (* 4 (car (n-f w x))))))
                     (equal (caddr (n-f (cons (wb) w) x))
                            (* 3 (caddr (n-f w x))))))
       :hints (("goal"
                :use ((:instance rotation-values (w w) (x x))
                      (:instance n-f-b-r (w w) (x x))
                      (:instance n-f (w w) (x x))
                      (:instance n-f (w (cons (wb) w)) (x x)))
                :in-theory (disable acl2-sqrt int-point n-f rotation weak-wordp)
                ))
       )
     )

    (local
     (defthmd n-mod3-b-r-lemma1
       (implies (and (weak-wordp w)
                     (equal x (acl2-sqrt 2)))
                (equal (n-mod3 (cons (wb) w) x)
                       (cons (mod (+ (car (n-f w x))  (car (cdr (n-f w x)))) 3)
                             (cons (mod (+ (car (cdr (n-f w x))) (car (n-f w x))) 3) (cons 0 nil))))
                )
       :hints (("goal"
                :use (
                      (:instance n-mod3 (w (cons (wb) w)) (x x))
                      (:instance n-mod3-b-r-lemma1-1 (a 0) (c (caddr (n-f w x))))
                      (:instance n-mod3-b-r-lemma1-5 (b (cadr (n-f w x))) (c (car (n-f w x))))
                      (:instance n-mod3-b-r-lemma1-6 (w w) (x x))
                      )
                :in-theory (disable int-point rotation reducedwordp acl2-sqrt n-f mod)
                :do-not-induct t
                )
               )
       )
     )

    (local
     (defthmd n-mod3-b-r-1
       (implies (and (integerp x)
                     (integerp y)
                     (not (equal y 0)))
                (integerp (mod x y)))
       )
     )

    (defthmd n-mod3-b-r
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (equal (n-mod3 (cons (wb) w) x)
                      (cons (mod (+ (car (n-mod3 w x))  (car (cdr (n-mod3 w x)))) 3)
                            (cons (mod (+ (car (cdr (n-mod3 w x))) (car (n-mod3 w x))) 3) (cons 0 nil))))
               )
      :hints (("goal"
               :use (
                     (:instance n-mod3-b-r-lemma1 (w w) (x x))
                     (:instance n-mod3-b-r-lemma1-6 (w w) (x x))
                     (:instance n-mod3-b-r-1 (x (cadr (n-f w x))) (y 3))
                     (:instance n-mod3-b-r-1 (x (car (n-f w x))) (y 3))
                     (:instance mod-+-frgrp
                                (x (cadr (n-f w x)))
                                (y (car (n-f w x)))
                                (z 3))

                     (:instance mod-+-frgrp
                                (y (cadr (n-f w x)))
                                (x (car (n-f w x)))
                                (z 3))
                     (:instance n-mod3-=)

                     )
               :in-theory nil
               :do-not-induct t
               ))
      )
    )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;n(b-inv)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


  (encapsulate
    ()

    (local
     (defthmd n-mod3-b-inv-r-lemma1-1
       (implies (and (integerp a)
                     (integerp c))
                (equal (mod (+ a (* 3 c))  3)
                       (mod a 3)
                       )
                )
       )
     )

    (local
     (defthmd n-mod3-b-inv-r-lemma1-3
       (equal (- b (* 4 c))
              (- (- b c) (* 3 c)))
       )
     )

    (local
     (defthmd n-mod3-b-inv-r-lemma1-4
       (equal (+  (* 2 b) c)
              (+ (- c b) (* 3 b)))
       )
     )

    (local
     (defthmd n-mod3-b-inv-r-lemma1-5
       (implies (and (integerp b)
                     (integerp c))
                (and (equal (- b (* 4 c))
                            (- (- b c) (* 3 c)))
                     (equal (mod (- b (* 4 c)) 3)
                            (mod (- b  c) 3))
                     (equal (mod (+ (* 2 b) c) 3)
                            (mod (- c b) 3))))
       :hints (("goal"
                :use ((:instance n-mod3-b-inv-r-lemma1-3 (b b) (c c))
                      (:instance n-mod3-b-inv-r-lemma1-1 (a (- b c)) (c (- c)))
                      (:instance n-mod3-b-inv-r-lemma1-4 (b b) (c c))
                      (:instance n-mod3-b-inv-r-lemma1-1 (a (- c b)) (c b))
                      )
                ))
       )
     )

    (local
     (defthmd n-mod3-b-inv-r-lemma1-6
       (implies (and (weak-wordp w)
                     (equal x (acl2-sqrt 2)))
                (and (integerp (car (n-f w x)))
                     (integerp (cadr (n-f w x)))
                     (integerp (caddr (n-f w x)))
                     (equal (caddr (n-f (cons (wb-inv) w) x)) (* 3 (caddr (n-f w x))))
                     (equal (cadr (n-f (cons (wb-inv) w) x))
                            (+ (cadr (n-f w x))
                               (- (* 4 (car (n-f w x))))))
                     (equal (car (n-f (cons (wb-inv) w) x))
                            (+ (* 2 (cadr (n-f w x)))
                               (car (n-f w x)))))

                )
       :hints (("goal"
                :use ((:instance rotation-values (w w) (x x))
                      (:instance n-f-b-inv-r (w w) (x x))
                      (:instance n-f (w w) (x x))
                      (:instance n-f (w (cons (wb-inv) w)) (x x)))
                :in-theory (disable int-point acl2-sqrt rotation reducedwordp mod weak-wordp n-f int-point)
                :do-not-induct t
                ))
       )
     )

    (local
     (defthmd n-mod3-b-inv-r-lemma1
       (implies (and (weak-wordp w)
                     (equal x (acl2-sqrt 2)))
                (equal (n-mod3 (cons (wb-inv) w) x)
                       (cons (mod (- (car (n-f w x))  (car (cdr (n-f w x)))) 3)
                             (cons (mod (- (car (cdr (n-f w x))) (car (n-f w x))) 3) (cons 0 nil))))
                )
       :hints (("goal"
                :use (
                      (:instance n-mod3 (w (cons (wa) w)) (x x))
                      (:instance n-mod3-b-inv-r-lemma1-1 (a 0) (c (caddr (n-f w x))))
                      (:instance n-mod3-b-inv-r-lemma1-5 (b (cadr (n-f w x))) (c (car (n-f w x))))
                      (:instance n-mod3-b-inv-r-lemma1-6 (w w) (x x))
                      )
                :in-theory (disable int-point rotation reducedwordp acl2-sqrt n-f mod)
                :do-not-induct t
                )
               )
       )
     )

    (local
     (defthmd n-mod3-b-inv-r-1
       (implies (and (integerp x)
                     (integerp y)
                     (not (equal y 0)))
                (integerp (mod x y)))
       )
     )

    (defthmd n-mod3-b-inv-r
      (implies (and (weak-wordp w)
                    (equal x (acl2-sqrt 2)))
               (equal (n-mod3 (cons (wb-inv) w) x)
                      (cons (mod (- (car (n-mod3 w x))  (car (cdr (n-mod3 w x)))) 3)
                            (cons (mod (- (car (cdr (n-mod3 w x))) (car (n-mod3 w x))) 3) (cons 0 nil))))
               )
      :hints (("goal"
               :use (
                     (:instance n-mod3-b-inv-r-lemma1 (w w) (x x))
                     (:instance n-mod3-b-inv-r-lemma1-6 (w w) (x x))
                     (:instance n-mod3-b-inv-r-1 (x (cadr (n-f w x))) (y 3))
                     (:instance n-mod3-b-inv-r-1 (x (caddr (n-f w x))) (y 3))
                     (:instance mod--frgrp
                                (x (cadr (n-f w x)))
                                (y (car (n-f w x)))
                                (z 3))

                     (:instance mod--frgrp
                                (y (cadr (n-f w x)))
                                (x (car (n-f w x)))
                                (z 3))
                     (:instance n-mod3-=)

                     )
               :in-theory nil
               :do-not-induct t
               ))
      )
    )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defthmd n-mod3-nil
    (equal (n-mod3 nil (acl2-sqrt 2))
           '(0 1 0)))


  (defthmd weak-cons-car-cdr
    (implies (and (character-listp x)
                  (not (atom x)))
             (equal (cons (car x) (cdr x)) x))
    )

  (defthmd n-mod3-a-r-wa
    (implies (and (weak-wordp w)
                  (equal (car w) (wa))
                  (equal x (acl2-sqrt 2)))
             (equal (n-mod3 w x)
                    (cons 0 (cons (mod (- (car (cdr (n-mod3 (cdr w) x)))  (car (cdr (cdr (n-mod3 (cdr w) x))))) 3)
                                  (cons (mod (- (car (cdr (cdr (n-mod3 (cdr w) x)))) (car (cdr (n-mod3 (cdr w) x)))) 3) nil)))

                    )
             )
    :hints (("goal"
             :use (
                   (:instance n-mod3-a-r (w (cdr w)) (x x))
                   (:instance weak-word-cdr (x w))
                   (:instance weak-cons-car-cdr (x w))
                   (:instance character-listp-word (x w))
                   )
             :in-theory (disable n-mod3 weak-wordp acl2-sqrt)
             :do-not-induct t
             ))

    )

  (defthmd n-mod3-a-inv-r-wa-inv
    (implies (and (weak-wordp w)
                  (equal (car w) (wa-inv))
                  (equal x (acl2-sqrt 2)))
             (equal (n-mod3 w x)
                    (cons 0 (cons (mod (+ (car (cdr (n-mod3 (cdr w) x)))  (car (cdr (cdr (n-mod3 (cdr w) x))))) 3)
                                  (cons (mod (+ (car (cdr (cdr (n-mod3 (cdr w) x)))) (car (cdr (n-mod3 (cdr w) x)))) 3) nil)))

                    )
             )
    :hints (("goal"
             :use (
                   (:instance n-mod3-a-inv-r (w (cdr w)) (x x))
                   (:instance weak-word-cdr (x w))
                   (:instance weak-cons-car-cdr (x w))
                   (:instance character-listp-word (x w))
                   )
             :in-theory (disable n-mod3 weak-wordp acl2-sqrt)
             :do-not-induct t
             ))
    )

  (defthmd n-mod3-b-r-wb
    (implies (and (weak-wordp w)
                  (equal (car w) (wb))
                  (equal x (acl2-sqrt 2)))
             (equal (n-mod3 w x)
                    (cons (mod (+ (car (n-mod3 (cdr w) x))  (car (cdr (n-mod3 (cdr w) x)))) 3)
                          (cons (mod (+ (car (cdr (n-mod3 (cdr w) x))) (car (n-mod3 (cdr w) x))) 3) (cons 0 nil))))
             )
    :hints (("goal"
             :use (
                   (:instance n-mod3-b-r (w (cdr w)) (x x))
                   (:instance weak-word-cdr (x w))
                   (:instance weak-cons-car-cdr (x w))
                   (:instance character-listp-word (x w))
                   )
             :in-theory (disable n-mod3 weak-wordp acl2-sqrt)
             :do-not-induct t
             ))
    )

  (defthmd n-mod3-b-inv-r-wb-inv
    (implies (and (weak-wordp w)
                  (equal (car w) (wb-inv))
                  (equal x (acl2-sqrt 2)))
             (equal (n-mod3 w x)
                    (cons (mod (- (car (n-mod3 (cdr w) x))  (car (cdr (n-mod3 (cdr w) x)))) 3)
                          (cons (mod (- (car (cdr (n-mod3 (cdr w) x))) (car (n-mod3 (cdr w) x))) 3) (cons 0 nil))))
             )
    :hints (("goal"
             :use (
                   (:instance n-mod3-b-inv-r (w (cdr w)) (x x))
                   (:instance weak-word-cdr (x w))
                   (:instance weak-cons-car-cdr (x w))
                   (:instance character-listp-word (x w))
                   )
             :in-theory (disable n-mod3 weak-wordp acl2-sqrt)
             :do-not-induct t
             ))
    )

  (defthmd reducedword-cdr
    (implies (reducedwordp x)
             (reducedwordp (cdr x)))
    )

  (defthmd n-mod3-red-lemma-final
    (implies (and (reducedwordp w)
                  (equal x (acl2-sqrt 2))
                  (> (len w) 0))
             (cond ((equal (car w) (wa))
                    (or (equal (n-mod3 w x) '(0 1 2))
                        (equal (n-mod3 w x) '(0 2 1)))
                    )
                   ((equal (car w) (wa-inv))
                    (or (equal (n-mod3 w x) '(0 1 1))
                        (equal (n-mod3 w x) '(0 2 2))))
                   ((equal (car w) (wb))
                    (or (equal (n-mod3 w x) '(1 1 0))
                        (equal (n-mod3 w x) '(2 2 0))))
                   ((equal (car w) (wb-inv))
                    (or (equal (n-mod3 w x) '(2 1 0))
                        (equal (n-mod3 w x) '(1 2 0))))
                   )
             )

    :hints (
            ("goal"
             :in-theory (e/d (reducedwordp) (acl2-sqrt n-mod3))
             )
            ("subgoal *1/1"
             :cases ((> (len (cdr w)) 0)
                     (= (len (cdr w)) 0))
             )
            ("subgoal *1/1.1"
             :cases ((equal (car w) (wa))
                     (equal (car w) (wa-inv))
                     (equal (car w) (wb))
                     (equal (car w) (wb-inv))
                     )
             :use ((:instance sqrt-2-lemmas)
                   (:instance n-mod3-nil)
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance n-mod3-a-r-wa (w w) (x x))
                   (:instance n-mod3-a-inv-r-wa-inv (w w) (x x))
                   (:instance n-mod3-b-r-wb (w w) (x x))
                   (:instance n-mod3-b-inv-r-wb-inv (w w) (x x))
                   )
             :in-theory (disable acl2-sqrt m-* n-mod3)
             )

            ("subgoal *1/1.2"
             :cases ((equal (car w) (wa))
                     (equal (car w) (wa-inv))
                     (equal (car w) (wb))
                     (equal (car w) (wb-inv))
                     )
             :use (:instance reducedword-cdr (x w))
             :in-theory (disable n-mod3 acl2-sqrt)
             )
            ("subgoal *1/1.2.1"
             :cases ((equal (car (cdr w)) (wa))
                     (equal (car (cdr w)) (wa-inv))
                     (equal (car (cdr w)) (wb))
                     (equal (car (cdr w)) (wb-inv))
                     )
             :use ((:instance reducedwordp=>weak-wordp (x w))
                   (:instance n-mod3-b-inv-r-wb-inv (w w) (x x)))
             )
            ("subgoal *1/1.2.2"
             :cases ((equal (car (cdr w)) (wa))
                     (equal (car (cdr w)) (wa-inv))
                     (equal (car (cdr w)) (wb))
                     (equal (car (cdr w)) (wb-inv))
                     )
             :use ((:instance reducedwordp=>weak-wordp (x w))
                   (:instance n-mod3-b-r-wb (w w) (x x)))
             )
            ("subgoal *1/1.2.3"
             :cases ((equal (car (cdr w)) (wa))
                     (equal (car (cdr w)) (wa-inv))
                     (equal (car (cdr w)) (wb))
                     (equal (car (cdr w)) (wb-inv))
                     )
             :use ((:instance reducedwordp=>weak-wordp (x w))
                   (:instance n-mod3-a-inv-r-wa-inv (w w) (x x)))
             )
            ("subgoal *1/1.2.4"
             :cases ((equal (car (cdr w)) (wa))
                     (equal (car (cdr w)) (wa-inv))
                     (equal (car (cdr w)) (wb))
                     (equal (car (cdr w)) (wb-inv))
                     )
             :use ((:instance reducedwordp=>weak-wordp (x w))
                   (:instance n-mod3-a-r-wa (w w) (x x)))
             )
            )
    )

  (defthmd n-mod3-red-lemma-=
    (implies (and (reducedwordp w)
                  (equal x (acl2-sqrt 2))
                  (> (len w) 0))
             (or (equal (n-mod3 w x) '(0 1 2))
                 (equal (n-mod3 w x) '(0 2 1))
                 (equal (n-mod3 w x) '(0 1 1))
                 (equal (n-mod3 w x) '(0 2 2))
                 (equal (n-mod3 w x) '(1 1 0))
                 (equal (n-mod3 w x) '(2 2 0))
                 (equal (n-mod3 w x) '(2 1 0))
                 (equal (n-mod3 w x) '(1 2 0))
                 )
             )

    :hints (
            ("goal"
             :use (:instance n-mod3-red-lemma-final (w w) (x x))
             :in-theory (e/d () (acl2-sqrt n-mod3))
             )
            )
    )
  )

(encapsulate
  ()
  (local (include-book "arithmetic-5/support/expt" :dir :system))

  (defthmd intep-expt-n
    (implies (and (integerp n)
                  (> n 0))
             (integerp (expt 3 n)))
    :hints (("goal"
             :in-theory (enable expt)
             ))
    )

  (defthmd 31/3-integerp
    (implies (integerp c)
             (equal (* 1/3 3 c) c))
    )

  (local
   (defthmd 3*int-mod-=0
     (implies (and (integerp c)
                   (>= c 0))
              (equal (mod (* 3 c) 3)
                     0
                     )
              )
     :hints (("goal"
              :use (:instance 31/3-integerp (c c))
              :in-theory (enable mod)
              ))
     )
   )

  (defthmd expt-3-n-lemma
    (implies (integerp n)
             (equal (* 3 (expt 3 (+ n -1))) (expt 3 n)))
    )

  (defthmd n-mod3-3-n-=0-1
    (implies (acl2-numberp y)
             (and (equal (* 3 1/3 3 1/3 y) y)
                  (equal (* 3 1/3 y) y)))
    )

  (defthmd n-mod3-3-n-=0
    (implies (and (integerp n)
                  (> n 0))
             (equal (mod (expt 3 n) 3) 0))
    :hints (("goal"
             :in-theory (disable mod)
             )
            ("subgoal *1/5"
             :use (
                   (:instance 3*int-mod-=0 (c (expt 3 (- n 1))))
                   (:instance intep-expt-n (n (- n 1)))
                   (:instance n-mod3-3-n-=0-1 (y (expt 3 n)))
                   (:instance expt-3-n-lemma (n n)))
             )
            )
    )

  (defthmd n-mod3-rotation=id-1
    (implies (and (array2p name m1)
                  (acl2-numberp (aref2 name m1 0 0))
                  (acl2-numberp (aref2 name m1 1 0))
                  (acl2-numberp (aref2 name m1 2 0))
                  (equal (first (dimensions name m1)) 3)
                  (equal (second (dimensions name m1)) 1)
                  (m-= m1 (point-p)))
             (and (equal (aref2 name m1 0 0) 0)
                  (equal (aref2 name m1 1 0) 1)
                  (equal (aref2 name m1 2 0) 0)))
    :hints (("goal"
             :use (:instance array2p-alist2p (name name) (l m1))
             :in-theory (enable aref2 default header alist2p array2p m-= m-=-row-1 m-=-row)
             :do-not-induct t
             )
            )
    )

  (defthmd n-mod3-rotation=id-2
    (implies (and (reducedwordp w)
                  (equal x (acl2-sqrt 2))
                  (symbolp name)
                  (m-= (rotation w x) (id-rotation)))
             (and (m-= (m-* (rotation w x) (point-p)) (point-p))
                  (array2p name (m-* (rotation w x) (point-p)))
                  (equal (first (dimensions name (m-* (rotation w x) (point-p)))) 3)
                  (equal (second (dimensions name (m-* (rotation w x) (point-p)))) 1)
                  )
             )
    :hints (("goal"
             :use ((:instance rotation-props (w w) (name name))
                   (:instance reducedwordp=>weak-wordp (x w))
                   )
             :in-theory (enable array2p dimensions header)
             :do-not-induct t

             ))
    )

  (defthmd n-mod3-rotation=id-4
    (implies (reducedwordp w)
             (integerp (len w))))

  (defthmd n-mod3-rotation=id
    (implies (and (reducedwordp w)
                  (equal x (acl2-sqrt 2))
                  (> (len w) 0)
                  (m-= (rotation w x) (id-rotation)))
             (equal (n-mod3 w x) '(0 0 0)))
    :hints (("goal"
             :use (
                   (:instance n-mod3-rotation=id-2 (w w) (x x) (name '$arg1))
                   (:instance acl2-nump-rot (w w) (name '$arg1) (x x))
                   (:instance n-mod3-rotation=id-1 (m1 (m-* (rotation w x) (point-p))) (name '$arg1))
                   (:instance sqrt-2-lemmas)
                   (:instance rotation-props (w w) (name '$arg1))
                   (:instance n-mod3-3-n-=0 (n (len w)))
                   (:instance reducedwordp=>weak-wordp (x w))
                   )
             :do-not-induct t
             )
            )
    )

  (defthmd rotaion-not=id
    (implies (and (reducedwordp w)
                  (equal x (acl2-sqrt 2))
                  (> (len w) 0))
             (not (m-= (rotation w x) (id-rotation))))
    :hints (("goal"
             :use ((:instance n-mod3-red-lemma-= (w w))
                   (:instance n-mod3-rotation=id (w w)))
             ))
    )
  )


(defthmd rot-a*rot-b=rot-a+b
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(equal x (acl2-sqrt 2)))
	   (m-= (m-* (rotation a x) (rotation b x)) (rotation (append a b) x)))
  :hints (("goal"
	   :in-theory (disable acl2-sqrt)
	   )
	  ("subgoal *1/1"
	   :use (:instance funs-lemmas-1 (x x))
	   :in-theory (disable acl2-sqrt)
	   )
	  )
  )

(encapsulate
  ()

  (local
   (defthmd rot-a-rota-fix-a-ind-1-1
     (implies (and (weak-wordp a)
                   (weak-wordp (cdr a))
                   (not (atom a))
                   (word-fix (cdr a))
                   (reducedwordp (word-fix (cdr a))))
              (m-= (rotation (word-fix (list (car a) (car (word-fix (cdr a)))))
                             (acl2-sqrt 2))
                   (rotation (list (car a) (car (word-fix (cdr a))))
                             (acl2-sqrt 2))))
     :hints (("goal"
              :cases((and (equal (car a) (wa)) (equal (car (word-fix (cdr a))) (wa)))
                     (and (equal (car a) (wa)) (equal (car (word-fix (cdr a))) (wa-inv)))
                     (and (equal (car a) (wa)) (equal (car (word-fix (cdr a))) (wb)))
                     (and (equal (car a) (wa)) (equal (car (word-fix (cdr a))) (wb-inv)))
                     (and (equal (car a) (wa-inv)) (equal (car (word-fix (cdr a))) (wa)))
                     (and (equal (car a) (wa-inv)) (equal (car (word-fix (cdr a))) (wa-inv)))
                     (and (equal (car a) (wa-inv)) (equal (car (word-fix (cdr a))) (wb)))
                     (and (equal (car a) (wa-inv)) (equal (car (word-fix (cdr a))) (wb-inv)))
                     (and (equal (car a) (wb)) (equal (car (word-fix (cdr a))) (wa)))
                     (and (equal (car a) (wb)) (equal (car (word-fix (cdr a))) (wa-inv)))
                     (and (equal (car a) (wb)) (equal (car (word-fix (cdr a))) (wb)))
                     (and (equal (car a) (wb)) (equal (car (word-fix (cdr a))) (wb-inv)))
                     (and (equal (car a) (wb-inv)) (equal (car (word-fix (cdr a))) (wa)))
                     (and (equal (car a) (wb-inv)) (equal (car (word-fix (cdr a))) (wa-inv)))
                     (and (equal (car a) (wb-inv)) (equal (car (word-fix (cdr a))) (wb)))
                     (and (equal (car a) (wb-inv)) (equal (car (word-fix (cdr a))) (wb-inv)))
                     )
              :use ((:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                    (:instance funs-lemmas-2 (x (acl2-sqrt 2))))
              :in-theory (disable acl2-sqrt)
              :do-not-induct t
              ))
     )
   )

  (local
   (defthmd rot-a-rota-fix-a-ind-1
     (implies (and (not (atom a))
                   (equal x (acl2-sqrt 2))
                   (word-fix (cdr a))
                   (weak-wordp a))
              (m-= (rotation (word-fix a) x)
                   (m-* (rotation (append (list (car a)) (list (car (word-fix (cdr a))))) x)
                        (rotation (cdr (word-fix (cdr a))) x))))
     :hints (("goal"
              :use ((:instance compose-assoc-lemma-export (x (list (car a))) (y (cdr a)))
                    (:instance weak-word-cdr (x a))
                    (:instance lemma3 (x (word-fix (cdr a))))
                    (:instance character-listp-word (x (cdr a)))
                    (:instance word-fix-rev-lemma3-12 (x (car a)) (y (word-fix (cdr a))))
                    (:instance weak-wordp-equivalent (x (cdr a)))
                    (:instance rot-a*rot-b=rot-a+b
                               (a (word-fix (append (list (car a)) (list (car (word-fix (cdr a)))))))
                               (b (cdr (word-fix (cdr a))))
                               (x x))
                    (:instance weak-wordp-equivalent (x (append (list (car a)) (list (car (word-fix (cdr a)))))))
                    (:instance weak-wordp-equivalent (x (cdr a)))
                    (:instance character-listp-word (x (word-fix (cdr a))))
                    (:instance lemma11 (x a))
                    (:instance rot-a-rota-fix-a-ind-1-1 (a a))
                    )
              :do-not-induct t
              :in-theory (disable word-fix append rotation acl2-sqrt weak-wordp reducedwordp)
              )
             ("subgoal 10"
              :in-theory (enable weak-wordp)
              )
             ("subgoal 9"
              :in-theory (enable weak-wordp)
              )
             ("subgoal 8"
              :in-theory (enable weak-wordp)
              )
             ("subgoal 4"
              :in-theory (enable weak-wordp)
              )
             ("subgoal 2"
              :in-theory (enable weak-wordp)
              )
             ("subgoal 5"
              :in-theory (enable append weak-wordp)
              )
             )
     )
   )

  (local
   (defthmd rot-a-rota-fix-a-ind
     (implies (and (not (atom a))
                   (m-= (rotation (word-fix (cdr a))
                                  (acl2-sqrt 2))
                        (rotation (cdr a) (acl2-sqrt 2)))
                   (weak-wordp a))
              (m-= (rotation (word-fix a) (acl2-sqrt 2))
                   (rotation a (acl2-sqrt 2))))
     :hints (("goal"
              :cases ((word-fix (cdr a))
                      (not (word-fix (cdr a))))
              :do-not-induct t
              )
             ("subgoal 2"
              :cases ((equal (car (word-fix (cdr a))) (wa))
                      (equal (car (word-fix (cdr a))) (wa-inv))
                      (equal (car (word-fix (cdr a))) (wb))
                      (equal (car (word-fix (cdr a))) (wb-inv))
                      )
              :use (
                    (:instance weak-word-cdr (x a))
                    (:instance weak-wordp-equivalent (x (cdr a)))
                    (:instance rot-a-rota-fix-a-ind-1 (a a) (x (acl2-sqrt 2)))
                    (:instance lemma3 (x a))
                    (:instance rotation (w a) (x (acl2-sqrt 2)))
                    (:instance lemma3 (x (word-fix (cdr a))))
                    (:instance rot-a*rot-b=rot-a+b
                               (a (list (car (word-fix (cdr a)))))
                               (b (cdr (word-fix (cdr a))))
                               (x (acl2-sqrt 2)))
                    (:instance reduced-cdr (x (word-fix (cdr a))))
                    )
              :in-theory (disable acl2-sqrt word-fix)
              )
             )
     )
   )

  (defthmd rot-a-rot-fix-a
    (implies (and (weak-wordp a)
                  (equal x (acl2-sqrt 2)))
             (m-= (rotation (word-fix a) x) (rotation a x))
             )
    :hints (("goal"
             :in-theory (disable acl2-sqrt)
             )
            ("subgoal *1/9"
             :use (:instance rot-a-rota-fix-a-ind (a a))
             )
            ("subgoal *1/7"
             :use (:instance rot-a-rota-fix-a-ind (a a))
             )
            ("subgoal *1/5"
             :use (:instance rot-a-rota-fix-a-ind (a a))
             )
            ("subgoal *1/3"
             :use (:instance rot-a-rota-fix-a-ind (a a))
             )
            )
    )
  )

(defthmd rot-a+b
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(equal x (acl2-sqrt 2)))
	   (m-= (rotation (append a b) x) (rotation (compose a b) x)))
  :hints (("goal"
	   :use ((:instance closure-weak-word (x a) (y b))
		 (:instance reducedwordp=>weak-wordp (x a))
		 (:instance reducedwordp=>weak-wordp (x b))
		 (:instance rot-a-rot-fix-a (a (append a b)))
		 )
	   :in-theory (disable acl2-sqrt rotation)
	   :do-not-induct nil
	   )
	  )
  )

(defthmd rot-a*rot-b-=
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(equal x (acl2-sqrt 2)))
	   (m-= (m-* (rotation a x) (rotation b x)) (rotation (compose a b) x)))
  :hints (("goal"
	   :use ((:instance rot-a*rot-b=rot-a+b (a a) (b b) (x x))
		 (:instance rot-a+b (a a) (b b) (x x)))
	   :in-theory (disable acl2-sqrt)
	   ))
  )

(defthmd m-*rot-rot-inv=id
  (implies (and (reducedwordp p)
		(equal x (acl2-sqrt 2)))
	   (m-= (m-* (rotation p x) (rotation (word-inverse p) x)) (id-rotation)))
  :hints (("goal"
	   :use ((:instance rot-a*rot-b-= (a p) (b (word-inverse p)))
		 (:instance reduced-inverse (x p))
		 (:instance reducedwordp-word-inverse (x p)))
	   :in-theory (disable acl2-sqrt compose word-inverse reducedwordp)
	   ))
  )

(defthmd array2p=>a=b=>a*c=b*c
  (implies (and (array2p name a)
		(array2p name b)
		(array2p name c)
		(m-= a b))
	   (m-= (m-* a c) (m-* b c)))
  )

(defthmd rot-a*rot-b=id
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(equal x (acl2-sqrt 2))
		(m-= (rotation a x) (rotation b x)))
	   (m-= (rotation (compose a (word-inverse b)) x) (id-rotation)))
  :hints (("goal"
	   :use ((:instance array2p=>a=b=>a*c=b*c
			    (a (rotation a x))
			    (name '$arg1)
			    (b (rotation b x))
			    (c (rotation (word-inverse b) x)))
		 (:instance rot-a*rot-b-= (a a) (b (word-inverse b)))
		 (:instance rot-a*rot-b-= (a b) (b (word-inverse b)))
		 (:instance reducedwordp-word-inverse (x b))
		 (:instance m-*rot-rot-inv=id (p b))
		 (:instance rotation-props (w a) (name '$arg1))
		 (:instance rotation-props (w b) (name '$arg1))
		 (:instance reducedwordp=>weak-wordp (x a))
		 (:instance reducedwordp=>weak-wordp (x b))
		 (:instance reducedwordp=>weak-wordp (x (word-inverse b)))
		 (:instance rotation-props (w (word-inverse b)) (name '$arg1))
		 )
	   :in-theory (disable acl2-sqrt compose word-inverse reducedwordp)
	   ))
  )

(defthmd redword-a-b-len=0
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(equal (len (compose a (word-inverse b))) 0))
	   (equal (compose a (word-inverse b)) '()))
  )

(defthmd a!=b=>rot-a!=rot-b-1
  (implies (and (reducedwordp a)
		(reducedwordp b)
		(not (atom a))
		(not (atom b))
		(not (equal a b))
		(equal x (acl2-sqrt 2)))
	   (not (m-= (rotation a x) (rotation b x))))
  :hints (("goal"
	   :cases ((> (len (compose a (word-inverse b))) 0)
		   (= (len (compose a (word-inverse b))) 0))
	   :do-not-induct t
	   )
	  ("subgoal 2"
	   :use ((:instance rot-a*rot-b=id (a a) (b b) (x x))
		 (:instance reducedwordp-word-inverse (x b))
		 (:instance closure-prop (x a) (y (word-inverse b)))
		 (:instance rotaion-not=id (w (compose a (word-inverse b))) (x x))
		 )

	   )
	  ("subgoal 1"
	   :use ((:instance reducedwordp-word-inverse (x b))
		 (:instance assoc-prop (x a) (y (word-inverse b)) (z b))
		 (:instance redword-a-b-len=0 (a a) (b b))
		 (:instance inv-inv-x=x (x b))
		 (:instance reduced-inverse (x (word-inverse b)))
		 (:instance word-fix=reducedwordp (x a))
		 (:instance word-fix=reducedwordp (x b)))
	   :in-theory (disable acl2-sqrt word-fix rotation reducedwordp word-inverse)
	   :do-not-induct t
	   )
	  )
  )

(defthmd a!=b=>rot-a!=rot-b
  (implies (and (reducedwordp a)
		(reducedwordp b)
     		(not (equal a b))
		(equal x (acl2-sqrt 2)))
	   (not (m-= (rotation a x) (rotation b x))))
  :hints (("goal"
	   :cases ((and (not (atom a)) (not (atom b)))
		   (and (not (atom a)) (atom b))
		   (and (atom a) (not (atom b))))
	   :in-theory (disable acl2-sqrt)
	   :do-not-induct t
	   )
	  ("subgoal 3"
	   :use ((:instance a!=b=>rot-a!=rot-b-1 (a a) (b b) (x x))
		 )
	   )
	  ("subgoal 2"
	   :use ((:instance rotaion-not=id (w a))
		 )
	   )
	  ("subgoal 1"
	   :use ((:instance rotaion-not=id (w b))
		 )
	   )
	  )
  )
