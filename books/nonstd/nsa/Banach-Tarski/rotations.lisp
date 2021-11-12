; Banach-Tarski theorem
;
; Proof that every element of the free group is a rotation in R^3.
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

(include-book "free-group")
(include-book "supportive-theorems")

(defun r3-matrixp (m)
  (and (array2p :fake-name m)
       (equal (r m) (c m))
       (equal (r m) 3)
       (realp (aref2 :fake-name m 0 0))
       (realp (aref2 :fake-name m 0 1))
       (realp (aref2 :fake-name m 0 2))
       (realp (aref2 :fake-name m 1 0))
       (realp (aref2 :fake-name m 1 1))
       (realp (aref2 :fake-name m 1 2))
       (realp (aref2 :fake-name m 2 0))
       (realp (aref2 :fake-name m 2 1))
       (realp (aref2 :fake-name m 2 2))
       )
  )

(defun r3-m-determinant (m)
  (declare (xargs :guard (and (array2p :fake-name m)
			      (equal (r m) (c m))
			      (equal (r m) 3))
		  :verify-guards nil))
  (+ (* (aref2 :fake-name m 0 0) (- (* (aref2 :fake-name m 1 1) (aref2 :fake-name m 2 2))
                                    (* (aref2 :fake-name m 1 2) (aref2 :fake-name m 2 1))))
     (* (- (aref2 :fake-name m 0 1)) (- (* (aref2 :fake-name m 1 0) (aref2 :fake-name m 2 2))
                                        (* (aref2 :fake-name m 1 2) (aref2 :fake-name m 2 0))))
     (* (aref2 :fake-name m 0 2) (- (* (aref2 :fake-name m 1 0) (aref2 :fake-name m 2 1))
                                    (* (aref2 :fake-name m 1 1) (aref2 :fake-name m 2 0))))
     )
  )

(local
 (defthm realp-r3-m-determinant
   (implies (r3-matrixp m)
	    (realp (r3-m-determinant m)))
   )
 )

(defthm
  array2p-alist2p-fname
  (implies (array2p :fake-name l)
	   (alist2p :fake-name l)))

(local
 (defthm
   aref2-m-*-1
   (implies (and (array2p :fake-name m1)
		 (array2p :fake-name m2)
		 (equal (second (dimensions :fake-name m1))
			(first  (dimensions :fake-name m2)))
		 (integerp i)
		 (integerp j)
		 (>= i 0)
		 (>= j 0)
		 (< i (first (dimensions :fake-name m1)))
		 (< j (second (dimensions :fake-name m2))))
	    (equal (aref2 :fake-name (m-* m1 m2) i j)
		   (dot m1
			m2
			i
			(+ -1 (second (dimensions :fake-name m1)))
			j)))
   :hints (("goal"
	    :use (:instance aref2-m-* (m1 m1) (m2 m2) (i i) (j j))
	    :in-theory (enable aref2 header default))))
 )

(encapsulate
  ()
  (local
   (defthm lemma1
     (implies (r3-matrixp m1)
              (m-= (m-* m1 (id-rotation)) m1))
     :hints (("goal"
              :use ((:instance right-unity-of-m-1-for-m-* (m1 m1) (name :fake-name))
                    (:instance normalize-dimensions-name (name '$arg) (l m1))
                    (:instance array2p-alist2p-fname (l m1)))
              :in-theory (enable header dimensions default m-*)
              )))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))
  (defthmd det-lemma
    (implies (and (r3-matrixp m1)
                  (r3-matrixp m2)
                  )
             (equal (r3-m-determinant (m-* m1 m2)) (* (r3-m-determinant m1) (r3-m-determinant m2))))
    :hints (("goal"
             :in-theory (enable r3-matrixp r3-m-determinant realp acl2-numberp)
             ))
    )
  )

(defun r3-m-inverse (m)
  `((:header :dimensions (3 3)
	     :maximum-length 10)
    ((0 . 0) . ,(/ (- (* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 2 2))
		      (* (aref2 '$arg1 m 2 1) (aref2 '$arg1 m 1 2)))
		   (r3-m-determinant m)))
    ((0 . 1) . ,(/ (- (* (aref2 '$arg1 m 0 2) (aref2 '$arg1 m 2 1))
		      (* (aref2 '$arg1 m 2 2) (aref2 '$arg1 m 0 1)))
		   (r3-m-determinant m)))
    ((0 . 2) . ,(/ (- (* (aref2 '$arg1 m 0 1) (aref2 '$arg1 m 1 2))
		      (* (aref2 '$arg1 m 1 1) (aref2 '$arg1 m 0 2)))
		   (r3-m-determinant m)))
    ((1 . 0) . ,(/ (- (* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 2 0))
		      (* (aref2 '$arg1 m 2 2) (aref2 '$arg1 m 1 0)))
		   (r3-m-determinant m)))
    ((1 . 1) . ,(/ (- (* (aref2 '$arg1 m 0 0) (aref2 '$arg1 m 2 2))
		      (* (aref2 '$arg1 m 2 0) (aref2 '$arg1 m 0 2)))
		   (r3-m-determinant m)))
    ((1 . 2) . ,(/ (- (* (aref2 '$arg1 m 0 2) (aref2 '$arg1 m 1 0))
		      (* (aref2 '$arg1 m 1 2) (aref2 '$arg1 m 0 0)))
		   (r3-m-determinant m)))
    ((2 . 0) . ,(/ (- (* (aref2 '$arg1 m 1 0) (aref2 '$arg1 m 2 1))
		      (* (aref2 '$arg1 m 2 0) (aref2 '$arg1 m 1 1)))
		   (r3-m-determinant m)))
    ((2 . 1) . ,(/ (- (* (aref2 '$arg1 m 0 1) (aref2 '$arg1 m 2 0))
		      (* (aref2 '$arg1 m 2 1) (aref2 '$arg1 m 0 0)))
		   (r3-m-determinant m)))
    ((2 . 2) . ,(/ (- (* (aref2 '$arg1 m 0 0) (aref2 '$arg1 m 1 1))
		      (* (aref2 '$arg1 m 1 0) (aref2 '$arg1 m 0 1)))
		   (r3-m-determinant m)))
    )
  )

(local
 (defthm array2p-r3-m-inverse
   (implies (r3-matrixp m)
	    (array2p :fake-name (r3-m-inverse m)))
   :hints (("goal"
	    :in-theory (enable array2p header dimensions)
	    :do-not-induct t
	    ))
   )
 )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  ;; Thanks to Eric McCarthy (mccarthy@kestrel.edu), Alessandro Coglio (coglio@kestrel.edu),
  ;; and Eric Smith (eric.smith@kestrel.edu) for assisting me in proving the below lemma.

  (defthm r3-m-inverse-=
    (implies (r3-matrixp m)
             (and (equal (aref2 :fakename (r3-m-inverse m) 0 0)
                         (/ (- (* (aref2 :fakename m 1 1) (aref2 :fakename m 2 2))
                               (* (aref2 :fakename m 2 1) (aref2 :fakename m 1 2)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 0 1)
                         (/ (- (* (aref2 :fakename m 0 2) (aref2 :fakename m 2 1))
                               (* (aref2 :fakename m 2 2) (aref2 :fakename m 0 1)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 0 2)
                         (/ (- (* (aref2 :fakename m 0 1) (aref2 :fakename m 1 2))
                               (* (aref2 :fakename m 1 1) (aref2 :fakename m 0 2)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 1 0)
                         (/ (- (* (aref2 :fakename m 1 2) (aref2 :fakename m 2 0))
                               (* (aref2 :fakename m 2 2) (aref2 :fakename m 1 0)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 1 1)
                         (/ (- (* (aref2 :fakename m 0 0) (aref2 :fakename m 2 2))
                               (* (aref2 :fakename m 2 0) (aref2 :fakename m 0 2)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 1 2)
                         (/ (- (* (aref2 :fakename m 0 2) (aref2 :fakename m 1 0))
                               (* (aref2 :fakename m 1 2) (aref2 :fakename m 0 0)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 2 0)
                         (/ (- (* (aref2 :fakename m 1 0) (aref2 :fakename m 2 1))
                               (* (aref2 :fakename m 2 0) (aref2 :fakename m 1 1)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 2 1)
                         (/ (- (* (aref2 :fakename m 0 1) (aref2 :fakename m 2 0))
                               (* (aref2 :fakename m 2 1) (aref2 :fakename m 0 0)))
                            (r3-m-determinant m)))
                  (equal (aref2 :fakename (r3-m-inverse m) 2 2)
                         (/ (- (* (aref2 :fakename m 0 0) (aref2 :fakename m 1 1))
                               (* (aref2 :fakename m 1 0) (aref2 :fakename m 0 1)))
                            (r3-m-determinant m)))
                  (equal (r (r3-m-inverse m)) (c (r3-m-inverse m)))
                  (equal (r (r3-m-inverse m)) 3)
                  )
             )
    :hints (("goal"
             :in-theory (e/d (r3-m-inverse dimensions header) (r3-m-determinant aref2))
             :expand ((:free (i j) (aref2 :fake-name
                                          (list '(:header :dimensions (3 3)
                                                          :maximum-length 10)
                                                (cons '(0 . 0)
                                                      (+ (* (/ (r3-m-determinant m))
                                                            (aref2 :fake-name m 1 1)
                                                            (aref2 :fake-name m 2 2))
                                                         (- (* (/ (r3-m-determinant m))
                                                               (aref2 :fake-name m 1 2)
                                                               (aref2 :fake-name m 2 1)))))
                                                (cons '(0 . 1)
                                                      (+ (- (* (/ (r3-m-determinant m))
                                                               (aref2 :fake-name m 0 1)
                                                               (aref2 :fake-name m 2 2)))
                                                         (* (/ (r3-m-determinant m))
                                                            (aref2 :fake-name m 0 2)
                                                            (aref2 :fake-name m 2 1))))
                                                (cons '(0 . 2)
                                                      (+ (* (/ (r3-m-determinant m))
                                                            (aref2 :fake-name m 0 1)
                                                            (aref2 :fake-name m 1 2))
                                                         (- (* (/ (r3-m-determinant m))
                                                               (aref2 :fake-name m 0 2)
                                                               (aref2 :fake-name m 1 1)))))
                                                (cons '(1 . 0)
                                                      (+ (- (* (/ (r3-m-determinant m))
                                                               (aref2 :fake-name m 1 0)
                                                               (aref2 :fake-name m 2 2)))
                                                         (* (/ (r3-m-determinant m))
                                                            (aref2 :fake-name m 2 0)
                                                            (aref2 :fake-name m 1 2))))
                                                (cons '(1 . 1)
                                                      (+ (* (/ (r3-m-determinant m))
                                                            (aref2 :fake-name m 0 0)
                                                            (aref2 :fake-name m 2 2))
                                                         (- (* (/ (r3-m-determinant m))
                                                               (aref2 :fake-name m 0 2)
                                                               (aref2 :fake-name m 2 0)))))
                                                (cons '(1 . 2)
                                                      (+ (- (* (/ (r3-m-determinant m))
                                                               (aref2 :fake-name m 0 0)
                                                               (aref2 :fake-name m 1 2)))
                                                         (* (/ (r3-m-determinant m))
                                                            (aref2 :fake-name m 1 0)
                                                            (aref2 :fake-name m 0 2))))
                                                (cons '(2 . 0)
                                                      (+ (* (/ (r3-m-determinant m))
                                                            (aref2 :fake-name m 1 0)
                                                            (aref2 :fake-name m 2 1))
                                                         (- (* (/ (r3-m-determinant m))
                                                               (aref2 :fake-name m 1 1)
                                                               (aref2 :fake-name m 2 0)))))
                                                (cons '(2 . 1)
                                                      (+ (- (* (/ (r3-m-determinant m))
                                                               (aref2 :fake-name m 0 0)
                                                               (aref2 :fake-name m 2 1)))
                                                         (* (/ (r3-m-determinant m))
                                                            (aref2 :fake-name m 0 1)
                                                            (aref2 :fake-name m 2 0))))
                                                (cons '(2 . 2)
                                                      (+ (* (/ (r3-m-determinant m))
                                                            (aref2 :fake-name m 0 0)
                                                            (aref2 :fake-name m 1 1))
                                                         (- (* (/ (r3-m-determinant m))
                                                               (aref2 :fake-name m 0 1)
                                                               (aref2 :fake-name m 1 0))))))
                                          i j)))
             ))
    )
  )

(local
 (defthm r3-m-inverse-realp
   (implies (r3-matrixp m)
	    (and (realp (aref2 :fake-name (r3-m-inverse m) 0 0))
		 (realp (aref2 :fake-name (r3-m-inverse m) 0 1))
		 (realp (aref2 :fake-name (r3-m-inverse m) 0 2))
		 (realp (aref2 :fake-name (r3-m-inverse m) 1 0))
		 (realp (aref2 :fake-name (r3-m-inverse m) 1 1))
		 (realp (aref2 :fake-name (r3-m-inverse m) 1 2))
		 (realp (aref2 :fake-name (r3-m-inverse m) 2 0))
		 (realp (aref2 :fake-name (r3-m-inverse m) 2 1))
		 (realp (aref2 :fake-name (r3-m-inverse m) 2 2)))
	    )
   :hints (("goal"
	    :use ((:instance  r3-m-inverse-= (m m))
		  (:instance realp-r3-m-determinant (m m)))
	    :in-theory (e/d (r3-matrixp) (r3-m-determinant aref2))
	    ))
   )
 )

(local
 (defthm r3-matrixp-m-inverse
   (implies (r3-matrixp m)
            (r3-matrixp (r3-m-inverse m)))
   :hints (("goal"
            :use ((:instance r3-m-inverse-realp (m m))
                  (:instance r3-m-inverse-= (m m))
                  (:instance array2p-r3-m-inverse (m m)))
            ))))

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

(defthm r3-matrixp-m1*m2-is-r3-matrixp
  (implies (and (r3-matrixp m1)
                (r3-matrixp m2))
           (r3-matrixp (m-* m1 m2)))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (local
   (defthmd lemma-100-1
     (implies (and (realp a)
                   (not (= a 0)))
              (equal (/ a a) 1)))
   )

  (local
   (defthm lemma-1
     (implies (and
               (realp (aref2 :fake-name m 0 0))
               (realp (aref2 :fake-name m 0 1))
               (realp (aref2 :fake-name m 0 2))
               (realp (aref2 :fake-name m 1 0))
               (realp (aref2 :fake-name m 1 1))
               (realp (aref2 :fake-name m 1 2))
               (realp (aref2 :fake-name m 2 0))
               (realp (aref2 :fake-name m 2 1))
               (realp (aref2 :fake-name m 2 2))
               (not (equal (+ (* (aref2 :fake-name m 0 0)
                                 (aref2 :fake-name m 1 1)
                                 (aref2 :fake-name m 2 2))
                              (* (aref2 :fake-name m 0 1)
                                 (aref2 :fake-name m 2 0)
                                 (aref2 :fake-name m 1 2))
                              (* (aref2 :fake-name m 1 0)
                                 (aref2 :fake-name m 0 2)
                                 (aref2 :fake-name m 2 1)))
                           (+ (* (aref2 :fake-name m 0 0)
                                 (aref2 :fake-name m 1 2)
                                 (aref2 :fake-name m 2 1))
                              (* (aref2 :fake-name m 0 1)
                                 (aref2 :fake-name m 1 0)
                                 (aref2 :fake-name m 2 2))
                              (* (aref2 :fake-name m 0 2)
                                 (aref2 :fake-name m 1 1)
                                 (aref2 :fake-name m 2 0))))))
              (equal (+ (* (aref2 :fake-name m 0 0)
                           (aref2 :fake-name m 1 1)
                           (aref2 :fake-name m 2 2)
                           (/ (+ (* (aref2 :fake-name m 0 0)
                                    (aref2 :fake-name m 1 1)
                                    (aref2 :fake-name m 2 2))
                                 (- (* (aref2 :fake-name m 0 0)
                                       (aref2 :fake-name m 1 2)
                                       (aref2 :fake-name m 2 1)))
                                 (- (* (aref2 :fake-name m 0 1)
                                       (aref2 :fake-name m 1 0)
                                       (aref2 :fake-name m 2 2)))
                                 (* (aref2 :fake-name m 0 1)
                                    (aref2 :fake-name m 2 0)
                                    (aref2 :fake-name m 1 2))
                                 (- (* (aref2 :fake-name m 0 2)
                                       (aref2 :fake-name m 1 1)
                                       (aref2 :fake-name m 2 0)))
                                 (* (aref2 :fake-name m 1 0)
                                    (aref2 :fake-name m 0 2)
                                    (aref2 :fake-name m 2 1)))))
                        (* (aref2 :fake-name m 0 1)
                           (aref2 :fake-name m 2 0)
                           (aref2 :fake-name m 1 2)
                           (/ (+ (* (aref2 :fake-name m 0 0)
                                    (aref2 :fake-name m 1 1)
                                    (aref2 :fake-name m 2 2))
                                 (- (* (aref2 :fake-name m 0 0)
                                       (aref2 :fake-name m 1 2)
                                       (aref2 :fake-name m 2 1)))
                                 (- (* (aref2 :fake-name m 0 1)
                                       (aref2 :fake-name m 1 0)
                                       (aref2 :fake-name m 2 2)))
                                 (* (aref2 :fake-name m 0 1)
                                    (aref2 :fake-name m 2 0)
                                    (aref2 :fake-name m 1 2))
                                 (- (* (aref2 :fake-name m 0 2)
                                       (aref2 :fake-name m 1 1)
                                       (aref2 :fake-name m 2 0)))
                                 (* (aref2 :fake-name m 1 0)
                                    (aref2 :fake-name m 0 2)
                                    (aref2 :fake-name m 2 1)))))
                        (* (aref2 :fake-name m 1 0)
                           (aref2 :fake-name m 0 2)
                           (aref2 :fake-name m 2 1)
                           (/ (+ (* (aref2 :fake-name m 0 0)
                                    (aref2 :fake-name m 1 1)
                                    (aref2 :fake-name m 2 2))
                                 (- (* (aref2 :fake-name m 0 0)
                                       (aref2 :fake-name m 1 2)
                                       (aref2 :fake-name m 2 1)))
                                 (- (* (aref2 :fake-name m 0 1)
                                       (aref2 :fake-name m 1 0)
                                       (aref2 :fake-name m 2 2)))
                                 (* (aref2 :fake-name m 0 1)
                                    (aref2 :fake-name m 2 0)
                                    (aref2 :fake-name m 1 2))
                                 (- (* (aref2 :fake-name m 0 2)
                                       (aref2 :fake-name m 1 1)
                                       (aref2 :fake-name m 2 0)))
                                 (* (aref2 :fake-name m 1 0)
                                    (aref2 :fake-name m 0 2)
                                    (aref2 :fake-name m 2 1))))))
                     (+ 1
                        (* (aref2 :fake-name m 0 0)
                           (aref2 :fake-name m 1 2)
                           (aref2 :fake-name m 2 1)
                           (/ (+ (* (aref2 :fake-name m 0 0)
                                    (aref2 :fake-name m 1 1)
                                    (aref2 :fake-name m 2 2))
                                 (- (* (aref2 :fake-name m 0 0)
                                       (aref2 :fake-name m 1 2)
                                       (aref2 :fake-name m 2 1)))
                                 (- (* (aref2 :fake-name m 0 1)
                                       (aref2 :fake-name m 1 0)
                                       (aref2 :fake-name m 2 2)))
                                 (* (aref2 :fake-name m 0 1)
                                    (aref2 :fake-name m 2 0)
                                    (aref2 :fake-name m 1 2))
                                 (- (* (aref2 :fake-name m 0 2)
                                       (aref2 :fake-name m 1 1)
                                       (aref2 :fake-name m 2 0)))
                                 (* (aref2 :fake-name m 1 0)
                                    (aref2 :fake-name m 0 2)
                                    (aref2 :fake-name m 2 1)))))
                        (* (aref2 :fake-name m 0 1)
                           (aref2 :fake-name m 1 0)
                           (aref2 :fake-name m 2 2)
                           (/ (+ (* (aref2 :fake-name m 0 0)
                                    (aref2 :fake-name m 1 1)
                                    (aref2 :fake-name m 2 2))
                                 (- (* (aref2 :fake-name m 0 0)
                                       (aref2 :fake-name m 1 2)
                                       (aref2 :fake-name m 2 1)))
                                 (- (* (aref2 :fake-name m 0 1)
                                       (aref2 :fake-name m 1 0)
                                       (aref2 :fake-name m 2 2)))
                                 (* (aref2 :fake-name m 0 1)
                                    (aref2 :fake-name m 2 0)
                                    (aref2 :fake-name m 1 2))
                                 (- (* (aref2 :fake-name m 0 2)
                                       (aref2 :fake-name m 1 1)
                                       (aref2 :fake-name m 2 0)))
                                 (* (aref2 :fake-name m 1 0)
                                    (aref2 :fake-name m 0 2)
                                    (aref2 :fake-name m 2 1)))))
                        (* (aref2 :fake-name m 0 2)
                           (aref2 :fake-name m 1 1)
                           (aref2 :fake-name m 2 0)
                           (/ (+ (* (aref2 :fake-name m 0 0)
                                    (aref2 :fake-name m 1 1)
                                    (aref2 :fake-name m 2 2))
                                 (- (* (aref2 :fake-name m 0 0)
                                       (aref2 :fake-name m 1 2)
                                       (aref2 :fake-name m 2 1)))
                                 (- (* (aref2 :fake-name m 0 1)
                                       (aref2 :fake-name m 1 0)
                                       (aref2 :fake-name m 2 2)))
                                 (* (aref2 :fake-name m 0 1)
                                    (aref2 :fake-name m 2 0)
                                    (aref2 :fake-name m 1 2))
                                 (- (* (aref2 :fake-name m 0 2)
                                       (aref2 :fake-name m 1 1)
                                       (aref2 :fake-name m 2 0)))
                                 (* (aref2 :fake-name m 1 0)
                                    (aref2 :fake-name m 0 2)
                                    (aref2 :fake-name m 2 1))))))))
     :hints (("goal"
              :use (:instance lemma-100-1
                              (a (/ (+ (* (aref2 :fake-name m 0 0)
                                          (aref2 :fake-name m 1 1)
                                          (aref2 :fake-name m 2 2))
                                       (- (* (aref2 :fake-name m 0 0)
                                             (aref2 :fake-name m 1 2)
                                             (aref2 :fake-name m 2 1)))
                                       (- (* (aref2 :fake-name m 0 1)
                                             (aref2 :fake-name m 1 0)
                                             (aref2 :fake-name m 2 2)))
                                       (* (aref2 :fake-name m 0 1)
                                          (aref2 :fake-name m 2 0)
                                          (aref2 :fake-name m 1 2))
                                       (- (* (aref2 :fake-name m 0 2)
                                             (aref2 :fake-name m 1 1)
                                             (aref2 :fake-name m 2 0)))
                                       (* (aref2 :fake-name m 1 0)
                                          (aref2 :fake-name m 0 2)
                                          (aref2 :fake-name m 2 1))))))
              :in-theory (disable aref2)
              ))
     )
   )

  (defthm m-*-m-m-inverse
    (implies (and (r3-matrixp m)
                  (not (= (r3-m-determinant m) 0)))
             (m-= (m-* m (r3-m-inverse m)) (id-rotation)))
    :hints (("goal"
             :use ((:instance array2p-alist2p (name :fake-name) (l m))
                   (:instance array2p-m-*-1
                              (m1 m)
                              (m2 (r3-m-inverse m))
                              (name :fake-name))
                   (:instance r3-m-inverse-= (m m))
                   (:instance dimensions-m-* (m1 m)
                              (m2 (r3-m-inverse m))
                              (name :fake-name))
                   (:instance array2p-alist2p (name :fake-name)
                              (l (r3-m-inverse m))))
             :in-theory (e/d (m-= dot) (aref2 r3-m-inverse))
             )
            ("subgoal 9"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 8"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 7"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 6"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 5"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 4"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 3"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 2"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 1"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            )
    )

  (defthm m-*-m-inverse-m
    (implies (and (r3-matrixp m)
                  (not (= (r3-m-determinant m) 0)))
             (m-= (m-* (r3-m-inverse m) m) (id-rotation)))
    :hints (("goal"
             :use ((:instance array2p-alist2p (name :fake-name) (l m))
                   (:instance array2p-m-*-1
                              (m2 m)
                              (m1 (r3-m-inverse m))
                              (name :fake-name))
                   (:instance r3-m-inverse-= (m m))
                   (:instance dimensions-m-* (m2 m)
                              (m1 (r3-m-inverse m))
                              (name :fake-name))
                   (:instance array2p-alist2p (name :fake-name)
                              (l (r3-m-inverse m))))
             :in-theory (e/d (m-= dot) (aref2 r3-m-inverse))
             )
            ("subgoal 9"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 8"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 7"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 6"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 5"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 4"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 3"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 2"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            ("subgoal 1"
             :in-theory (e/d (r3-m-inverse) (r3-m-determinant))
             )
            )
    )
  )

(defthmd
  associativity-of-m-*-1
  (equal (m-* m1 (m-* m2 m3))
         (m-* (m-* m1 m2) m3)))

(defthmd m1=m2=>a*m1=a*m2
  (implies (and (r3-matrixp m1)
                (r3-matrixp m2)
                (r3-matrixp a)
                (m-= m1 m2))
           (m-= (m-* a m1) (m-* a m2))))

(encapsulate
  ()

  (local
   (defthm lemma1
     (implies (and (r3-matrixp m1)
                   (r3-matrixp m2)
                   (equal (m-* m1 (id-rotation))
                          (m-* (id-rotation) m2)))
              (m-= m2 m1))
     :hints (("goal"
              :in-theory (e/d (m-= m-*) ())
              ))))

  (defthmd m1*m2=i
    (implies (and (r3-matrixp m1)
                  (not (= (r3-m-determinant m1) 0))
                  (r3-matrixp m2)
                  (m-= (m-* m1 m2) (id-rotation)))
             (m-= m2 (r3-m-inverse m1)))
    :hints (("goal"
             :use ((:instance lemma1 (m1 (r3-m-inverse m1)) (m2 m2))
                   (:instance array2p-r3-m-inverse (m m1))
                   (:instance right-unity-of-m-1-for-m-* (name :fake-name) (m1 m2))
                   (:instance left-unity-of-m-1-for-m-* (name :fake-name) (m1 (r3-m-inverse m1)))
                   (:instance r3-matrixp-m-inverse (m m1))
                   (:instance m1=m2=>a*m1=a*m2 (m1 (m-* m1 m2)) (m2 (id-rotation)) (a (r3-m-inverse m1)))
                   (:instance associativity-of-m-*-1 (m1 (r3-m-inverse m1)) (m2 m1) (m3 m2))
                   (:instance associativity-of-m-* (m1 (r3-m-inverse m1)) (m2 m1) (m3 m2))
                   (:instance r3-matrixp-m1*m2-is-r3-matrixp (m1 m1) (m2 m2)))
             :in-theory (e/d () ( m-= m-* id-rotation aref2 array2p alist2p associativity-of-m-* associativity-of-m-*-1 m1=m2=>a*m1=a*m2 r3-matrixp-m-inverse r3-matrixp-m1*m2-is-r3-matrixp r3-m-determinant r3-m-inverse )))
            )
    )
  )

(defthmd
  associativity-of-m-*-2
  (equal (m-* (m-* m1 m2) m3)
         (m-* m1 (m-* m2 m3))))

(defthmd
  associativity-of-m-*-3
  (equal (m-* m1 m2 m3)
         (m-* (m-* m1 m2) m3)))

(encapsulate
  ()
  (local
   (defthm lemma1
     (implies (r3-matrixp m1)
              (m-= (m-* m1 (id-rotation)) m1))
     :hints (("goal"
              :use ((:instance right-unity-of-m-1-for-m-* (m1 m1) (name :fake-name))
                    (:instance normalize-dimensions-name (name '$arg) (l m1))
                    (:instance array2p-alist2p-fname (l m1)))
              :in-theory (enable header dimensions default m-*)
              ))))

  (defthmd m*id=m
    (implies (r3-matrixp m1)
             (m-= (m-* m1 (id-rotation)) m1))
    :hints (("Goal"
             :use ((:instance lemma1))
             :in-theory nil
             )))

  (local
   (defthm lemma2
     (implies (r3-matrixp m1)
              (m-= (m-* (id-rotation) m1) m1))
     :hints (("goal"
              :use ((:instance left-unity-of-m-1-for-m-* (m1 m1) (name :fake-name))
                    (:instance normalize-dimensions-name (name '$arg) (l m1))
                    (:instance array2p-alist2p-fname (l m1)))
              :in-theory (enable header dimensions default m-*)
              ))))

  (defthmd id*m=m
    (implies (r3-matrixp m1)
             (m-= (m-* (id-rotation) m1) m1))
    :hints (("Goal"
             :use ((:instance lemma2))
             :in-theory nil
             )))

  (local
   (defthm lemma4
     (implies (and (r3-matrixp m1)
                   (r3-matrixp m2)
                   (r3-matrixp m3)
                   (r3-matrixp m4))
              (equal (m-* m1 m2 m3 m4) (m-* m1 (m-* m2 m3) m4)))))

  (local
   (defthm lemma5
     (implies (and (r3-matrixp a)
                   (r3-matrixp b)
                   (r3-matrixp c)
                   (r3-matrixp d)
                   (m-= b c))
              (m-= (m-* a b d) (m-* a c d)))))

  (local
   (defthm lemma6
     (implies (and (r3-matrixp x)
                   (r3-matrixp y)
                   (m-= x y)
                   (r3-matrixp z))
              (m-= (m-* x z) (m-* y z)))))

  (local
   (defthm lemma7
     (implies (and (r3-matrixp m1)
                   (not (= (r3-m-determinant m1) 0))
                   (r3-matrixp m2)
                   (not (= (r3-m-determinant m2) 0)))
              (m-= (m-* (m-* m1 m2) (m-* (r3-m-inverse m2) (r3-m-inverse m1))) (id-rotation)))
     :hints (("goal"
              :use ((:instance lemma4 (m1 m1) (m2 m2) (m3 (r3-m-inverse m2)) (m4 (r3-m-inverse m1)))
                    (:instance r3-matrixp-m-inverse (m m2))
                    (:instance m-*-m-m-inverse (m m1))
                    (:instance m-*-m-m-inverse (m m2))
                    (:instance lemma6 (x (m-* m1 (id-rotation))) (y m1) (z (r3-m-inverse m1)))
                    (:instance lemma5 (a m1) (b (m-* m2 (r3-m-inverse m2))) (c (id-rotation)) (d (r3-m-inverse m1)))
                    (:instance lemma1 (m1 m1))
                    (:instance associativity-of-m-*-3 (m1 m1) (m2 (id-rotation)) (m3 (r3-m-inverse m1))))
              :in-theory (e/d () (m-* m-= r3-matrixp r3-m-determinant r3-m-inverse aref2 lemma1 lemma4 lemma5 m-*-m-m-inverse r3-matrixp-m-inverse id-rotation lemma6))))))

  (local (in-theory nil))
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm m-inverse-m-*-m1-m2
    (implies (and (r3-matrixp m1)
                  (not (= (r3-m-determinant m1) 0))
                  (r3-matrixp m2)
                  (not (= (r3-m-determinant m2) 0)))
             (m-= (r3-m-inverse (m-* m1 m2))
                  (m-* (r3-m-inverse m2) (r3-m-inverse m1))))
    :hints (("goal"
             :use ((:instance m1*m2=i (m1 (m-* m1 m2)) (m2 (m-* (r3-m-inverse m2) (r3-m-inverse m1))))
                   (:instance r3-matrixp-m1*m2-is-r3-matrixp (m1 m1) (m2 m2))
                   (:instance realp-r3-m-determinant (m m1))
                   (:instance realp-r3-m-determinant (m m2))
                   (:instance r3-matrixp-m-inverse (m m1))
                   (:instance r3-matrixp-m-inverse (m m2))
                   (:instance r3-matrixp-m1*m2-is-r3-matrixp (m1 (r3-m-inverse m2)) (m2 (r3-m-inverse m1)))
                   (:instance r3-matrixp-m-inverse (m (m-* m1 m2)))
                   (:instance det-lemma (m1 m1) (m2 m2))
                   (:instance lemma7))
             ))))

(defun r3-rotationp (m)
  (and (r3-matrixp m)
       (= (r3-m-determinant m) 1)
       (m-= (r3-m-inverse m) (m-trans m)))
  )

(defthm rot*rot-is-rot
  (implies (and (r3-rotationp m1)
                (r3-rotationp m2))
           (r3-rotationp (m-* m1 m2)))
  :hints (("goal"
           :use ((:instance r3-matrixp-m1*m2-is-r3-matrixp (m1 m1) (m2 m2))
                 (:instance det-lemma (m1 m1) (m2 m2))
                 (:instance m-inverse-m-*-m1-m2 (m1 m1) (m2 m2))
                 (:instance m-trans-m-*=m-*-m-trans (m1 m1) (m2 m2) (name :fake-name))
                 (:instance array2p-alist2p (l m1) (name :fake-name))
                 (:instance array2p-alist2p (l m2) (name :fake-name))
                 )
           :in-theory (e/d (r3-matrixp r3-rotationp)
                           (m-* aref2 m-= m-trans r3-m-inverse r3-m-determinant))
           ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm base-rotations
    (implies (equal x (acl2-sqrt 2))
             (and (r3-rotationp (a-rotation x))
                  (r3-rotationp (a-inv-rotation x))
                  (r3-rotationp (b-rotation x))
                  (r3-rotationp (b-inv-rotation x))
                  (r3-rotationp (id-rotation))))
    :hints (("goal"
             :use ((:instance array2p-funs (y :fake-name))
                   (:instance sqrt-2-lemmas))
             :in-theory (e/d (aref2 m-=) (acl2-sqrt))
             ))
    )
  )

(defthmd reducedwordp-charlistp
  (implies (and (character-listp w)
                w)
           (equal (append (list (car w)) (cdr w)) w)))

(defthmd rotation-is-r3-rotationp-basecase
  (implies (equal x (acl2-sqrt 2))
           (and (r3-rotationp (rotation '(#\a) x))
                (r3-rotationp (rotation '(#\b) x))
                (r3-rotationp (rotation '(#\c) x))
                (r3-rotationp (rotation '(#\d) x))))
  :hints (("goal"
           :use ((:instance rot*rot-is-rot
                            (m1 (a-rotation x))
                            (m2 (id-rotation)))
                 (:instance rot*rot-is-rot
                            (m1 (b-rotation x))
                            (m2 (id-rotation)))
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation x))
                            (m2 (id-rotation)))
                 (:instance rot*rot-is-rot
                            (m1 (b-inv-rotation x))
                            (m2 (id-rotation)))
                 (:instance base-rotations (x x)))
           ))
  )

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthmd rotation-is-r3-rotationp-1
    (implies (and (weak-wordp w)
                  (equal x (acl2-sqrt 2)))
             (r3-rotationp (rotation w x)))
    :hints (("goal"
             :in-theory (disable acl2-sqrt)
             )
            ("subgoal *1/5"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            ("subgoal *1/4"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            ("subgoal *1/3"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            ("subgoal *1/2"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            ("subgoal *1/1"
             :use ((:instance character-listp-word (x w))
                   (:instance rotation-= (w w))
                   (:instance reducedwordp=>weak-wordp (x w))
                   (:instance funs-lemmas-1 (x x))
                   (:instance rotation-is-r3-rotationp-basecase (x x))
                   (:instance rot*rot-is-rot
                              (m1 (rotation (list (car w)) x))
                              (m2 (rotation (cdr w) x))))
             :in-theory (disable acl2-sqrt r3-rotationp aref2)
             )
            )
    )
  )

(defthmd rotation-is-r3-rotationp
  (implies (and (reducedwordp w)
                (equal x (acl2-sqrt 2)))
           (r3-rotationp (rotation w x)))
  :hints (("goal"
           :use ((:instance rotation-is-r3-rotationp-1 (w w) (x x))
                 (:instance reducedwordp=>weak-wordp (x w)))
           :in-theory nil
           )))
