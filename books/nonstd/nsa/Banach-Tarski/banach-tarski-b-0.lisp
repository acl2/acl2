; Banach-Tarski theorem
;
; Proof of the Banach-Tarski theorem on a solid ball centered at the origin except for the origin (B^3-0).
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

(include-book "banach-tarski-s2")

(defun cal-radius (p)
  (acl2-sqrt (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                (* (point-in-r3-z1 p) (point-in-r3-z1 p)))))

(defun point-p/r (p)
  `((:header :dimensions (3 1)
	     :maximum-length 15)
    ((0 . 0) . ,(/ (point-in-r3-x1 p) (cal-radius p)) )
    ((1 . 0) . ,(/ (point-in-r3-y1 p) (cal-radius p)) )
    ((2 . 0) . ,(/ (point-in-r3-z1 p) (cal-radius p)) )
    )
  )

(defthmd point-p/r=>1
  (and (equal (aref2 :fake-name (point-p/r p) 0 0) (/ (point-in-r3-x1 p) (cal-radius p)))
       (equal (aref2 :fake-name (point-p/r p) 1 0) (/ (point-in-r3-y1 p) (cal-radius p)))
       (equal (aref2 :fake-name (point-p/r p) 2 0) (/ (point-in-r3-z1 p) (cal-radius p))))
  :hints (("goal"
           :in-theory (e/d (aref2) (cal-radius))
           )))

(defthmd point-p/r=>2
  (and (equal (point-in-r3-x1 (point-p/r p)) (/ (point-in-r3-x1 p) (cal-radius p)))
       (equal (point-in-r3-y1 (point-p/r p)) (/ (point-in-r3-y1 p) (cal-radius p)))
       (equal (point-in-r3-z1 (point-p/r p)) (/ (point-in-r3-z1 p) (cal-radius p))))
  :hints (("goal"
           :in-theory (e/d (aref2) (cal-radius))
           )))

(defthmd pr3-point-p
  (implies (and (point-in-r3 p)
                (> (cal-radius p) 0)
                (realp (cal-radius p)))
           (point-in-r3 (point-p/r p)))
  :hints (("goal"
           :in-theory (e/d (array2p dimensions header aref2) (acl2-sqrt cal-radius))
           )))

(defun b3-0 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)))

(defun-sk b3-0-s2-1 (p)
  (exists p-s2
          (and (s2-def-p p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-s2 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-s2-1 p)))

(defthmd pr3=>r^2>=0
  (implies (point-in-r3 p)
           (and (>= (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                       (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                       (* (point-in-r3-z1 p) (point-in-r3-z1 p)))
                    0)
                (realp (cal-radius p))
                (realp (/ (cal-radius p)))
                (>= (cal-radius p) 0))))

(defthmd b3-0=>r^2>0
  (implies (b3-0 p)
           (and (realp (cal-radius p))
                (equal (* (cal-radius p) (cal-radius p))
                       (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                          (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                          (* (point-in-r3-z1 p) (point-in-r3-z1 p))))
                (> (* (cal-radius p) (cal-radius p)) 0)))
  :hints (("goal"
           :use ((:instance y-=-sqrt
                            (x (+ (* (point-in-r3-x1 p) (point-in-r3-x1 p))
                                  (* (point-in-r3-y1 p) (point-in-r3-y1 p))
                                  (* (point-in-r3-z1 p) (point-in-r3-z1 p))))
                            (y (cal-radius p)))
                 (:instance pr3=>r^2>=0 (p p)))
           :in-theory (disable acl2-sqrt y-=-sqrt)
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd b3-0-iff-b3-0-equiv-1-1
   (implies (and (realp d)
		 (realp a)
		 (realp b)
		 (realp c)
		 (equal x (/ a d))
		 (equal y (/ b d))
		 (equal z (/ c d)))
	    (equal (+ (* x x) (* y y) (* z z))
		   (/ (+ (* a a) (* b b) (* c c)) (* d d)))))

 (defthmd b3-0-iff-b3-0-equiv-1
   (implies (b3-0 p)
	    (s2-def-p (point-p/r p)))
   :hints (("goal"
	    :use ((:instance b3-0-s2-1-suff (p-s2 (point-p/r p)) (p p))
		  (:instance point-p/r=>1 (p p))
		  (:instance s2-def-p (point (point-p/r p)))
		  (:instance pr3-point-p (p p))
		  (:instance b3-0 (p p))
		  (:instance b3-0=>r^2>0 (p p))
		  (:instance b3-0-iff-b3-0-equiv-1-1
			     (d (cal-radius p))
			     (x (aref2 :fake-name (point-p/r p) 0 0))
			     (y (aref2 :fake-name (point-p/r p) 1 0))
			     (z (aref2 :fake-name (point-p/r p) 2 0))
			     (a (point-in-r3-x1 p))
			     (b (point-in-r3-y1 p))
			     (c (point-in-r3-z1 p)))

		  )
	    :in-theory (e/d () (point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 point-p/r cal-radius s2-def-p b3-0-s2 b3-0-s2-1 (:rewrite b3-0-s2-1-suff) pr3-point-p))
	    )))

 (defthmd b3-0-iff-b3-0-s2
   (iff (b3-0 p)
	(b3-0-s2 p))
   :hints (("goal"
	    :use ((:instance b3-0-s2-1-suff (p-s2 (point-p/r p)) (p p))
		  (:instance point-p/r=>1 (p p))
		  (:instance point-p/r=>2 (p p))
		  (:instance s2-def-p (point (point-p/r p)))
		  (:instance pr3-point-p (p p))
		  (:instance b3-0 (p p))
		  (:instance b3-0=>r^2>0 (p p))
		  (:instance b3-0-iff-b3-0-equiv-1 (p p))
		  (:instance b3-0-s2 (p p))
		  )
	    :in-theory (e/d () (point-in-r3 point-in-r3-x1 point-in-r3-y1 point-in-r3-z1 point-p/r cal-radius s2-def-p b3-0-s2 b3-0-s2-1 (:rewrite b3-0-s2-1-suff) pr3-point-p))
	    )))
 )

(defun-sk b3-0-set-a1-1 (p)
  (exists p-s2
          (and (set-a1 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a1 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a1-1 p)))

(defun-sk b3-0-set-a2-1 (p)
  (exists p-s2
          (and (set-a2 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a2 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a2-1 p)))

(defun-sk b3-0-set-a3-1 (p)
  (exists p-s2
          (and (set-a3 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a3 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a3-1 p)))

(defun-sk b3-0-set-a4-1 (p)
  (exists p-s2
          (and (set-a4 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a4 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a4-1 p)))

(defun-sk b3-0-set-a5-1 (p)
  (exists p-s2
          (and (set-a5 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a5 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a5-1 p)))

(defun-sk b3-0-set-a6-1 (p)
  (exists p-s2
          (and (set-a6 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a6 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a6-1 p)))

(defun-sk b3-0-set-a7-1 (p)
  (exists p-s2
          (and (set-a7 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a7 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a7-1 p)))

(defun-sk b3-0-set-a8-1 (p)
  (exists p-s2
          (and (set-a8 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a8 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a8-1 p)))

(defun-sk b3-0-set-a9-1 (p)
  (exists p-s2
          (and (set-a9 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a9 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a9-1 p)))

(defun-sk b3-0-set-a10-1 (p)
  (exists p-s2
          (and (set-a10 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a10 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a10-1 p)))

(defun-sk b3-0-set-a11-1 (p)
  (exists p-s2
          (and (set-a11 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a11 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a11-1 p)))

(defun-sk b3-0-set-a12-1 (p)
  (exists p-s2
          (and (set-a12 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a12 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a12-1 p)))

(defun-sk b3-0-set-a13-1 (p)
  (exists p-s2
          (and (set-a13 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a13 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a13-1 p)))

(defun-sk b3-0-set-a14-1 (p)
  (exists p-s2
          (and (set-a14 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a14 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a14-1 p)))

(defthmd b3-0=>a1-to-a14
  (implies (b3-0-s2 p)
           (or (b3-0-set-a1 p)
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
               (b3-0-set-a14 p)))
  :hints (("goal"
           :use ((:instance b3-0-s2 (p p))
                 (:instance b3-0-s2-1 (p p))
                 (:instance s2-equiv-1 (p (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a1 (p p))
                 (:instance b3-0-set-a1-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a2 (p p))
                 (:instance b3-0-set-a2-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a3 (p p))
                 (:instance b3-0-set-a3-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a4 (p p))
                 (:instance b3-0-set-a4-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a5 (p p))
                 (:instance b3-0-set-a5-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a6 (p p))
                 (:instance b3-0-set-a6-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a7 (p p))
                 (:instance b3-0-set-a7-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a8 (p p))
                 (:instance b3-0-set-a8-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a9 (p p))
                 (:instance b3-0-set-a9-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a10 (p p))
                 (:instance b3-0-set-a10-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a11 (p p))
                 (:instance b3-0-set-a11-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a12 (p p))
                 (:instance b3-0-set-a12-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a13 (p p))
                 (:instance b3-0-set-a13-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a14 (p p))
                 (:instance b3-0-set-a14-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd a1-to-a14=>b3-0
  (implies (or (b3-0-set-a1 p)
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
           (b3-0 p))
  :hints (("goal"
           :in-theory (disable b3-0-set-a1-1 b3-0-set-a2-1 b3-0-set-a3-1 b3-0-set-a4-1 b3-0-set-a5-1 b3-0-set-a6-1 b3-0-set-a7-1 b3-0-set-a8-1 b3-0-set-a9-1 b3-0-set-a10-1 b3-0-set-a11-1 b3-0-set-a12-1 b3-0-set-a13-1 b3-0-set-a14-1)
           )))

(defthmd b3-0-iff-a1-to-a14-1
  (iff (or (b3-0-s2 p)
           (b3-0 p))
       (or (b3-0-set-a1 p)
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
           (b3-0-set-a14 p)))
  :hints (("goal"
           :use ((:instance b3-0-iff-b3-0-s2 (p p))
                 (:instance b3-0=>a1-to-a14 (p p))
                 (:instance a1-to-a14=>b3-0 (p p)))
           :in-theory nil
           )))

;; proof that, b3-0 sets are disjoint.
;;
;; (skip-proofs
;;  (defthmd a1=>not-a2
;;    (implies (set-a1 p)
;;             (not (set-a2 p)))))

;; (defthmd n-p1=p2=>diff-n-p2
;;   (implies (and (m-= p1 p2)
;;                 (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (diff-n-s2-d-p p1))
;;            (diff-n-s2-d-p p2))
;;   :hints (("goal"
;;            :use ((:instance diff-n-s2-d-p (p p1))
;;                  (:instance diff-n-s2-d-p (p p2))
;;                  (:instance diff-n-s2-d-p-q (p p1))
;;                  (:instance diff-n-s2-d-p-q-1 (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p1)))
;;                             (p p1))
;;                  (:instance diff-n-s2-d-p-q-1-suff (w nil) (cp1 (choice-set-s2-d-p (diff-n-s2-d-p-q-witness p1)))
;;                             (p p2))
;;                  (:instance diff-n-s2-d-p-q-suff (p1 (diff-n-s2-d-p-q-witness p1)) (p p2))
;;                  )
;;            :in-theory nil
;;            )))


;; (defthmd p1=p2=>set-a1-p2
;;   (implies (and (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (set-a1 p1)
;;                 (m-= p1 p2))
;;            (set-a1 p2))
;;   :hints (("goal"
;;            :use ((:instance set-a1 (p p1))
;;                  (:instance m0 (p p1))
;;                  (:instance s2-not-e (point p1))
;;                  (:instance p1=p2-n-e-p1=>e-p2 (p2 p1) (p1 p2))
;;                  (:instance set-a1 (p p2))
;;                  (:instance m0 (p p2))
;;                  (:instance s2-d-p-equivalence-1 (p p1))
;;                  (:instance s2-d-p (point p1))
;;                  (:instance s2-d-p (point p2))
;;                  (:instance s2-def-p-p=>p1 (p p1) (p1 p2))
;;                  (:instance d-p-p=>d-p-p1 (p p2) (p1 p1))
;;                  (:instance s2-d-p-equivalence-1 (p p2))
;;                  (:instance n-p1=p2=>diff-n-p2 (p1 p1) (p2 p2))
;;                  (:instance s2-not-e (point p2))
;;                  )
;;            :in-theory nil
;;            )))

;; (defthmd disjoint-lemma-1
;;   (implies (and (point-in-r3 p1)
;;                 (point-in-r3 p2)
;;                 (equal (point-in-r3-x1 p2)
;;                        (point-in-r3-x1 p1))
;;                 (equal (point-in-r3-y1 p2)
;;                        (point-in-r3-y1 p1))
;;                 (equal (point-in-r3-z1 p2)
;;                        (point-in-r3-z1 p1)))
;;            (m-= p1 p2))
;;   :hints (("goal"
;;            :in-theory (enable m-=)
;;            )))

;; (defthmd disjoint-lemma
;;   (implies (b3-0-set-a1 p)
;;            (not (b3-0-set-a2 p)))
;;   :hints (("goal"
;;            :use ((:instance b3-0-set-a1 (p p))
;;                  (:instance b3-0-set-a1-1 (p p))
;;                  (:instance b3-0-set-a2 (p p))
;;                  (:instance b3-0-set-a2-1 (p p))
;;                  (:instance set-a1 (p (b3-0-set-a1-1-witness p)))
;;                  (:instance m0 (p (b3-0-set-a1-1-witness p)))
;;                  (:instance s2-d-p-equivalence-1 (p (b3-0-set-a1-1-witness p)))
;;                  (:instance s2-d-p (point (b3-0-set-a1-1-witness p)))
;;                  (:instance s2-def-p (point (b3-0-set-a1-1-witness p)))
;;                  (:instance set-a2 (p (b3-0-set-a2-1-witness p)))
;;                  (:instance r-1*m1 (p (b3-0-set-a2-1-witness p)))
;;                  (:instance p1=p2=>set-a1-p2 (p1 (b3-0-set-a1-1-witness p))
;;                             (p2 (b3-0-set-a2-1-witness p)))
;;                  (:instance disjoint-lemma-1 (p1 (b3-0-set-a1-1-witness p))
;;                             (p2 (b3-0-set-a2-1-witness p)))
;;                  (:instance a1=>not-a2 (p (b3-0-set-a2-1-witness p)))
;;                  )
;;            :in-theory nil
;;            )))

;; (defun-sk set-a-inv-a3-1 (point)
;;   (exists p
;;           (and (set-a3 p)
;;                (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) p)
;;                     point))))

;; (defun set-a-inv-a3 (p)
;;   (and (point-in-r3 p)
;;        (set-a-inv-a3-1 p)))

(defthmd m1=m2/a=>m1=s-*/a-m2
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (equal (point-in-r3-x1 p1)
                       (* a (point-in-r3-x1 p2)))
                (equal (point-in-r3-y1 p1)
                       (* a (point-in-r3-y1 p2)))
                (equal (point-in-r3-z1 p1)
                       (* a (point-in-r3-z1 p2))))
           (m-= p1 (s-* a p2)))
  :hints (("goal"
           :use ((:instance aref2-s-* (m p2) (a a))
                 (:instance dimensions-s-* (m p2) (a a)))
           :in-theory (e/d (m-=) (s-*))
           )))

(defthmd m-=m1m2=>r-m1=r-m2-1
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (m-= p1 p2))
           (and (equal (aref2 :fake-name p1 0 0) (aref2 :fake-name p2 0 0))
                (equal (aref2 :fake-name p1 1 0) (aref2 :fake-name p2 1 0))
                (equal (aref2 :fake-name p1 2 0) (aref2 :fake-name p2 2 0))))
  :hints (("goal"
           :in-theory (enable m-=)
           )))

(defthmd m-=m1m2=>r-m1=r-m2-2
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (r3-rotationp rot)
                (m-= (m-* rot p1) p2))
           (equal (+ (* (aref2 :fake-name p1 0 0) (aref2 :fake-name p1 0 0))
                     (* (aref2 :fake-name p1 1 0) (aref2 :fake-name p1 1 0))
                     (* (aref2 :fake-name p1 2 0) (aref2 :fake-name p1 2 0)))
                  (+ (* (aref2 :fake-name p2 0 0) (aref2 :fake-name p2 0 0))
                     (* (aref2 :fake-name p2 1 0) (aref2 :fake-name p2 1 0))
                     (* (aref2 :fake-name p2 2 0) (aref2 :fake-name p2 2 0)))))
  :hints (("goal"
           :use ((:instance rotation*point-on-s2 (p1 p1) (p2 (m-* rot p1)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (rot rot)
                            (p1 p1))
                 (:instance r3-rotationp (m rot))
                 (:instance m-=m1m2=>r-m1=r-m2-1 (p1 (m-* rot p1)) (p2 p2))
                 )
           :in-theory nil
           )))

(defthmd m-=m-*rot-p1=p2=>r-p1=r-p2
  (implies (and (point-in-r3 p1)
                (point-in-r3 p2)
                (r3-rotationp rot)
                (m-= (m-* rot p1) p2))
           (equal (cal-radius p1)
                  (cal-radius p2)))
  :hints (("goal"
           :use ((:instance m-=m1m2=>r-m1=r-m2-2 (p1 p1) (p2 p2) (rot rot))
                 )
           :in-theory (disable m-= m-* point-in-r3 r3-rotationp)
           )))

(defthmd pr3-p=>pr3-a*p
  (implies (and (point-in-r3 p)
                (realp a))
           (point-in-r3 (s-* a p))))

(defthmd xyz-p1=xyz-p2
  (implies (and (r3-matrixp rot)
                (point-in-r3 p1)
                (point-in-r3 p2)
                (point-in-r3 p3)
                (realp a)
                (m-= (m-* rot p2) p1)
                (m-= p3 (s-* a p2)))
           (and (equal (point-in-r3-x1 (m-* rot p3)) (* a (point-in-r3-x1 p1)))
                (equal (point-in-r3-y1 (m-* rot p3)) (* a (point-in-r3-y1 p1)))
                (equal (point-in-r3-z1 (m-* rot p3)) (* a (point-in-r3-z1 p1)))))
  :hints (("goal"
           :use ((:instance m-=-implies-equal-m-*-2
                            (m2 p3)
                            (m1 rot)
                            (m2-equiv (s-* a p2)))
                 (:instance m-*-s-*-right (m1 rot) (a a) (m2 p2) (name :fake-name))
                 (:instance aref2-s-* (a a) (m (m-* rot p2)))
                 (:instance r3-matrixp (m rot))
                 (:instance point-in-r3 (x p2))
                 (:instance m-=m1m2=>r-m1=r-m2-1 (p1 (m-* rot p3)) (p2 (s-* a p1)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p3)
                            (rot rot))
                 (:instance pr3-p=>pr3-a*p (a a) (p p1))
                 )
           :in-theory (e/d () (m-= m-* aref2 header dimensions array2p alist2p r3-matrixp point-in-r3))
           )))

(defun-sk b3-0-a-inv-b3-0-set-a3-1 (p)
  (exists p-s2
          (and (b3-0-set-a3 p-s2)
               (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) p-s2)
                    p))))

(defun b3-0-a-inv-b3-0-set-a3 (p)
  (and (point-in-r3 p)
       (b3-0-a-inv-b3-0-set-a3-1 p)))


(defun-sk b3-0-set-a-inv-a3-1 (p)
  (exists p-s2
          (and (set-a-inv-a3 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a-inv-a3 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a-inv-a3-1 p)))

(defthmd b3-0-a-1-a3-iff-a-1-b3-0-a3-1
  (implies (and (equal (point-in-r3-x1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (point-in-r3-x1 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                          (/ (cal-radius p))))
                (equal (point-in-r3-y1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (point-in-r3-y1 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                          (/ (cal-radius p))))
                (equal (point-in-r3-z1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (point-in-r3-z1 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                          (/ (cal-radius p)))))
           (and (equal (point-in-r3-x1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (/ (cal-radius p))
                          (point-in-r3-x1 (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                (equal (point-in-r3-z1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (/ (cal-radius p))
                          (point-in-r3-z1 (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                (equal (point-in-r3-y1
                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                       (* (/ (cal-radius p))
                          (point-in-r3-y1 (b3-0-a-inv-b3-0-set-a3-1-witness p)))))))

(defthmd b3-0-a-1-a3-iff-a-1-b3-0-a3-2
  (equal (* x y)
         (* y x)))


(defthmd b3-0-a-1-b3-0-a3=>b3-0-a-1-a3
  (implies (b3-0-a-inv-b3-0-set-a3 p)
           (b3-0-set-a-inv-a3 p))
  :hints (("goal"
           :use ((:instance b3-0-a-inv-b3-0-set-a3 (p p))
                 (:instance b3-0-a-inv-b3-0-set-a3-1 (p p))
                 (:instance b3-0-set-a3 (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance b3-0-set-a3-1 (p (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                 (:instance b3-0-set-a-inv-a3 (p p))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2 (p1 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                            (p2 p)
                            (rot (a-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0-set-a-inv-a3-1-suff
                            (p-s2 (m-* (a-inv-rotation (acl2-sqrt 2))
                                       (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                            (p p))
                 (:instance set-a-inv-a3 (p (m-* (a-inv-rotation (acl2-sqrt 2))
                                                 (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))))
                 (:instance set-a3 (p (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance wa-00 (p (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance wa-0 (p (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance s2-not-e (point (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance s2-def-p (point (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                            (rot (a-inv-rotation (acl2-sqrt 2))))
                 (:instance r3-rotationp (m (a-inv-rotation (acl2-sqrt 2))))
                 (:instance set-a-inv-a3-1-suff
                            (p (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                            (point (m-* (a-inv-rotation (acl2-sqrt 2))
                                        (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))))
                 (:instance xyz-p1=xyz-p2
                            (p1 p)
                            (p2 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                            (p3 (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                            (rot (a-inv-rotation (acl2-sqrt 2)))
                            (a (/ (cal-radius p))))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-a3-1-witness (b3-0-a-inv-b3-0-set-a3-1-witness p)))
                            (p2 (b3-0-a-inv-b3-0-set-a3-1-witness p))
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-1)
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 )
           :in-theory nil
           )))

(defthmd b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-1
  (implies (point-in-r3 p1)
           (m-= (m-* (a-rotation (acl2-sqrt 2)) (a-inv-rotation (acl2-sqrt 2)) p1)
                p1))
  :hints (("goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance associativity-of-m-*
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m3 p1))
                 )
           :in-theory (e/d () (a-rotation a-inv-rotation b-rotation b-inv-rotation acl2-sqrt m-= m-* (:executable-counterpart id-rotation) id-rotation associativity-of-m-* m-*point-id=point))
           )))

(defthmd b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-2
  (implies (and (equal
                 (point-in-r3-x1 (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p)))
                 (* (/ (cal-radius p))
                    (point-in-r3-x1 (m-* (a-rotation (acl2-sqrt 2)) p))))
                (equal
                 (point-in-r3-y1 (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p)))
                 (* (/ (cal-radius p))
                    (point-in-r3-y1 (m-* (a-rotation (acl2-sqrt 2)) p))))
                (equal
                 (point-in-r3-z1 (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p)))
                 (* (/ (cal-radius p))
                    (point-in-r3-z1 (m-* (a-rotation (acl2-sqrt 2)) p)))))
           (and (equal
                 (point-in-r3-x1 (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p)))
                 (* (point-in-r3-x1 (m-* (a-rotation (acl2-sqrt 2)) p))
                    (/ (cal-radius p))))
                (equal
                 (point-in-r3-y1 (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p)))
                 (* (point-in-r3-y1 (m-* (a-rotation (acl2-sqrt 2)) p))
                    (/ (cal-radius p))))
                (equal
                 (point-in-r3-z1 (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p)))
                 (* (point-in-r3-z1 (m-* (a-rotation (acl2-sqrt 2)) p))
                    (/ (cal-radius p)))))))

(defthmd b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-3
  (implies (point-in-r3 p1)
           (m-= (m-* (a-inv-rotation (acl2-sqrt 2)) (a-rotation (acl2-sqrt 2)) p1)
                p1))
  :hints (("goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance associativity-of-m-*
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (a-rotation (acl2-sqrt 2)))
                            (m3 p1))
                 )
           :in-theory (e/d () (a-rotation a-inv-rotation b-rotation b-inv-rotation acl2-sqrt m-= m-* (:executable-counterpart id-rotation) id-rotation associativity-of-m-* m-*point-id=point))
           )))

(defthmd b3-0-a-1-a3=>b3-0-a-1-b3-0-a3
  (implies (b3-0-set-a-inv-a3 p)
           (b3-0-a-inv-b3-0-set-a3 p))
  :hints (("goal"
           :use ((:instance b3-0-set-a-inv-a3 (p p))
                 (:instance b3-0-set-a-inv-a3-1 (p p))
                 (:instance set-a-inv-a3 (p (b3-0-set-a-inv-a3-1-witness p)))
                 (:instance set-a-inv-a3-1 (point (b3-0-set-a-inv-a3-1-witness p)))
                 (:instance b3-0-a-inv-b3-0-set-a3 (p p))
                 (:instance b3-0-a-inv-b3-0-set-a3-1-suff
                            (p p)
                            (p-s2 (m-* (a-rotation (acl2-sqrt 2)) p)))
                 (:instance b3-0-set-a3 (p (m-* (a-rotation (acl2-sqrt 2)) p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot (a-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (a-rotation (acl2-sqrt 2))))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-a-inv-a3-1-witness p))
                            (p2 p)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 (:instance set-a3 (p (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                 (:instance wa-00 (p (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                 (:instance wa-0 (p (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                 (:instance s2-not-e (point (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                 (:instance s2-def-p (point (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                 (:instance m-=-implies-equal-m-*-2
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m2 (m-* (a-inv-rotation (acl2-sqrt 2))
                                     (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                            (m2-equiv (b3-0-set-a-inv-a3-1-witness p)))
                 (:instance b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-1
                            (p1 (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                 (:instance m-*-s-*-right
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m2 p)
                            (name :fake-name)
                            (a (/ (cal-radius p))))
                 (:instance r3-matrixp (m (a-rotation (acl2-sqrt 2))))
                 (:instance array2p-alist2p

                            (name :fake-name)
                            (l (a-rotation (acl2-sqrt 2))))
                 (:instance point-in-r3 (x p))
                 (:instance normalize-dimensions-name (name '$arg) (l p))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l p))
                 (:instance m-=-implies-equal-m-*-2
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m2 (b3-0-set-a-inv-a3-1-witness p))
                            (m2-equiv (s-* (/ (cal-radius p)) p)))
                 (:instance b3-0-set-a3-1-suff
                            (p-s2 (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p)))
                            (p (m-* (a-rotation (acl2-sqrt 2)) p)))
                 (:instance m-=m1m2=>r-m1=r-m2-1
                            (p1 (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p)))
                            (p2 (s-* (/ (cal-radius p))
                                     (m-* (a-rotation (acl2-sqrt 2)) p))))
                 (:instance pr3-p=>pr3-a*p
                            (a (/ (cal-radius p)))
                            (p (m-* (a-rotation (acl2-sqrt 2)) p)))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (a (/ (cal-radius p)))
                            (m (m-* (a-rotation (acl2-sqrt 2)) p))
                            (i 0)
                            (j 0))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (a (/ (cal-radius p)))
                            (m (m-* (a-rotation (acl2-sqrt 2)) p))
                            (i 1)
                            (j 0))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (a (/ (cal-radius p)))
                            (m (m-* (a-rotation (acl2-sqrt 2)) p))
                            (i 2)
                            (j 0))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (p2 (m-* (a-rotation (acl2-sqrt 2)) p))
                            (rot (a-rotation (acl2-sqrt 2))))
                 (:instance point-in-r3-x1
                            (p (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                 (:instance point-in-r3-x1
                            (p (m-* (a-rotation (acl2-sqrt 2)) p)))
                 (:instance point-in-r3-y1
                            (p (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                 (:instance point-in-r3-y1
                            (p (m-* (a-rotation (acl2-sqrt 2)) p)))
                 (:instance point-in-r3-z1
                            (p (set-a-inv-a3-1-witness (b3-0-set-a-inv-a3-1-witness p))))
                 (:instance point-in-r3-z1
                            (p (m-* (a-rotation (acl2-sqrt 2)) p)))
                 (:instance b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-2)
                 (:instance b3-0-a-1-a3=>b3-0-a-1-b3-0-a3-3 (p1 p))
                 )
           :in-theory nil
           )))

(defthmd b3-0-a-1-b3-0-a3-iff-b3-0-a-1-a3
  (iff (b3-0-a-inv-b3-0-set-a3 p)
       (b3-0-set-a-inv-a3 p))
  :hints (("goal"
           :use ((:instance b3-0-a-1-a3=>b3-0-a-1-b3-0-a3)
                 (:instance b3-0-a-1-b3-0-a3=>b3-0-a-1-a3))
           )))


(defun-sk b3-0-a-inv-r-b3-0-set-a4-1 (p)
  (exists p-s2
          (and (b3-0-set-a4 p-s2)
               (m-= (m-* (a-inv-rotation (acl2-sqrt 2))
                         (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                         p-s2)
                    p))))

(defun b3-0-a-inv-r-b3-0-set-a4 (p)
  (and (point-in-r3 p)
       (b3-0-a-inv-r-b3-0-set-a4-1 p)))


(defun-sk b3-0-set-a-inv-r-a4-1 (p)
  (exists p-s2
          (and (set-a-inv-r-a4 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-a-inv-r-a4 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-a-inv-r-a4-1 p)))

(defthmd b3-0-a-1-r-b3-0-a4=>b3-0-a-1-r-a4
  (implies (b3-0-a-inv-r-b3-0-set-a4 p)
           (b3-0-set-a-inv-r-a4 p))
  :hints (("goal"
           :use ((:instance b3-0-a-inv-r-b3-0-set-a4 (p p))
                 (:instance b3-0-a-inv-r-b3-0-set-a4-1 (p p))
                 (:instance b3-0-set-a4 (p (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance b3-0-set-a4-1 (p (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance b3-0-set-a-inv-r-a4 (p p))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*rot-is-rot
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance b3-0-set-a-inv-r-a4-1-suff
                            (p-s2 (m-* (a-inv-rotation (acl2-sqrt 2))
                                       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                       (b3-0-set-a4-1-witness (b3-0-a-inv-r-b3-0-set-a4-1-witness p))))
                            (p p))
                 (:instance set-a-inv-r-a4
                            (p (m-* (a-inv-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                    (b3-0-set-a4-1-witness (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))))
                 (:instance set-a4 (p (b3-0-set-a4-1-witness (b3-0-a-inv-r-b3-0-set-a4-1-witness p))))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 (b3-0-a-inv-r-b3-0-set-a4-1-witness p))
                            (p2 p)
                            (rot (m-* (a-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d
                                       (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                       (point-on-s2-not-d)))))
                 (:instance associativity-of-m-*
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m3 (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b3-0-set-a4-1-witness (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                            (rot (m-* (a-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance r3-rotationp
                            (m (m-* (a-inv-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance associativity-of-m-*
                            (m1 (a-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m3 (b3-0-set-a4-1-witness (b3-0-a-inv-r-b3-0-set-a4-1-witness p))))
                 (:instance set-a-inv-r-a4-1-suff
                            (p (b3-0-set-a4-1-witness (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                            (point (m-* (a-inv-rotation (acl2-sqrt 2))
                                        (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                        (b3-0-set-a4-1-witness (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))))
                 (:instance xyz-p1=xyz-p2
                            (p1 p)
                            (p2 (b3-0-a-inv-r-b3-0-set-a4-1-witness p))
                            (p3 (b3-0-set-a4-1-witness (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                            (rot (m-* (a-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi)))
                                                   (point-on-s2-not-d))))
                            (a (/ (cal-radius p))))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-a4-1-witness (b3-0-a-inv-r-b3-0-set-a4-1-witness p)))
                            (p2 (b3-0-a-inv-r-b3-0-set-a4-1-witness p))
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 (b3-0-a-inv-r-b3-0-set-a4-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 (b3-0-a-inv-r-b3-0-set-a4-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 (b3-0-a-inv-r-b3-0-set-a4-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 )
           :in-theory nil
           )))

(defthmd b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-1
  (implies (and (m-= (m-* a-1 r wit-wit) wit)
                (m-= (m-* a a-1) id-1)
                (m-= (m-* id-1 r) r1)
                (m-= (m-* r-1 r1) id-2)
                (m-= (m-* id-2 wit-wit) wit-wit-1))
           (m-= wit-wit-1 (m-* r-1 a wit))))

(defthmd b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-2
  (implies (and (m-= wit-wit (m-* a b wit))
                (m-= wit s))
           (m-= wit-wit (m-* a b s))))

(defthmd b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-3
  (implies (and (m-= wit-wit (m-* r-1-rot (s-* a p)))
                (point-in-r3 wit-wit)
                (point-in-r3 (s-* a (m-* r-1-rot p)))
                (alist2p :fake-name p)
                (equal (cadr (dimensions :fake-name r-1-rot))
                       (car (dimensions :fake-name p)))
                (alist2p :fake-name r-1-rot))
           (and (equal (point-in-r3-x1 wit-wit) (* (point-in-r3-x1 (m-* r-1-rot p)) a))
                (equal (point-in-r3-y1 wit-wit) (* (point-in-r3-y1 (m-* r-1-rot p)) a))
                (equal (point-in-r3-z1 wit-wit) (* (point-in-r3-z1 (m-* r-1-rot p)) a))))
  :hints (("goal"
           :use ((:instance m-*-s-*-right
                            (name :fake-name)
                            (m1 r-1-rot)
                            (m2 p))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (a a)
                            (m (m-* r-1-rot p))
                            (i 0)
                            (j 0))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (a a)
                            (m (m-* r-1-rot p))
                            (i 1)
                            (j 0))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (a a)
                            (m (m-* r-1-rot p))
                            (i 2)
                            (j 0))
                 )
           :in-theory (e/d (m-=)(s-* m-* aref2 aref2-m-*))
           )))

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-4
   (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
			      0 (* 2 (acl2-pi))))
			  (point-on-s2-not-d))
	     (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
			   0 (* 2 (acl2-pi)))
			  (point-on-s2-not-d)))
	(id-rotation))
   :hints (("goal"
	    :use ((:instance r-t1*r-t2=r-t1+t2
			     (angle2 (exists-in-interval-but-not-in-angle-sequence-witness
				      0 (* 2 (acl2-pi))))
			     (angle1 (- (exists-in-interval-but-not-in-angle-sequence-witness
					 0 (* 2 (acl2-pi)))))
			     (u (point-on-s2-not-d)))
		  (:instance exists-point-on-s2-not-d-2)
		  (:instance s2-def-p (point (point-on-s2-not-d)))
		  (:instance witness-not-in-angle-sequence)
		  (:instance r-theta-0=id (u (point-on-s2-not-d)))
		  )
	    :in-theory (e/d () (point-on-s2-not-d rotation-3d s2-def-p point-in-r3 aref2 m-* rotation nth-angle-exists angles-seq alist2p))
	    )))
 )

(encapsulate
 ()

 (local (include-book "arithmetic/top" :dir :system))

 (defthmd b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-6
   (m-= (m-* (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
			   0 (* 2 (acl2-pi)))
			  (point-on-s2-not-d))
	     (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
			      0 (* 2 (acl2-pi))))
			  (point-on-s2-not-d)))
	(id-rotation))
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
		  (:instance r-theta-0=id (u (point-on-s2-not-d)))
		  )
	    :in-theory (e/d () (point-on-s2-not-d rotation-3d s2-def-p point-in-r3 aref2 m-* rotation nth-angle-exists angles-seq alist2p))
	    )))
 )

(defthmd b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-5
  (implies (and (m-= (m-* a-1-2 a) id-1)
                (m-= (m-* r r-1) id-2)
                (m-= (m-* a-1 id-2) a-1-2)
                (m-= (m-* id-1 p) p))
           (and (m-= (m-* a-1 r (m-* r-1 a) p)
                     p)
                (m-= (m-* a-1 r r-1 a p)
                     p))))

(defthmd b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4
  (implies (b3-0-set-a-inv-r-a4 p)
           (b3-0-a-inv-r-b3-0-set-a4 p))
  :hints (("goal"
           :use ((:instance b3-0-set-a-inv-r-a4 (p p))
                 (:instance b3-0-set-a-inv-r-a4-1 (p p))
                 (:instance set-a-inv-r-a4 (p (b3-0-set-a-inv-r-a4-1-witness p)))
                 (:instance set-a-inv-r-a4-1 (point (b3-0-set-a-inv-r-a4-1-witness p)))
                 (:instance b3-0-a-inv-r-b3-0-set-a4 (p p))
                 (:instance b3-0-a-inv-r-b3-0-set-a4-1-suff
                            (p p)
                            (p-s2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                       (a-rotation (acl2-sqrt 2)) p)))
                 (:instance b3-0-set-a4 (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                 0 (* 2 (acl2-pi))))
                                                             (point-on-s2-not-d))
                                                (a-rotation (acl2-sqrt 2))
                                                p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (a-rotation (acl2-sqrt 2)))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*rot-is-rot
                            (m2 (a-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance r3-rotationp (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                  0 (* 2 (acl2-pi))))
                                                              (point-on-s2-not-d))
                                                 (a-rotation (acl2-sqrt 2)))))
                 (:instance associativity-of-m-*
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (a-rotation (acl2-sqrt 2)))
                            (m3 p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-a-inv-r-a4-1-witness p))
                            (p2 p)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 (:instance set-a4 (p (set-a-inv-r-a4-1-witness (b3-0-set-a-inv-r-a4-1-witness p))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-1
                            (a-1 (a-inv-rotation (acl2-sqrt 2)))
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (wit-wit (set-a-inv-r-a4-1-witness (b3-0-set-a-inv-r-a4-1-witness p)))
                            (wit-wit-1 (set-a-inv-r-a4-1-witness (b3-0-set-a-inv-r-a4-1-witness p)))
                            (wit (b3-0-set-a-inv-r-a4-1-witness p))
                            (a (a-rotation (acl2-sqrt 2)))
                            (id-1 (id-rotation))
                            (r1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (id-2 (id-rotation)))
                 (:instance m-*point-id=point
                            (p1 (set-a-inv-r-a4-1-witness (b3-0-set-a-inv-r-a4-1-witness p))))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness
                                    0 (* 2 (acl2-pi)))))
                 (:instance r3-rotationp (m (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance id*m=m (m1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance m-*-s-*-right (m1 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                    0 (* 2 (acl2-pi))))
                                                                (point-on-s2-not-d))
                                                   (a-rotation (acl2-sqrt 2))))
                            (m2 p)
                            (name :fake-name)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-2
                            (wit-wit (set-a-inv-r-a4-1-witness (b3-0-set-a-inv-r-a4-1-witness p)))
                            (wit (b3-0-set-a-inv-r-a4-1-witness p))
                            (b (a-rotation (acl2-sqrt 2)))
                            (a (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                0 (* 2 (acl2-pi))))
                                            (point-on-s2-not-d)))
                            (s (s-* (/ (cal-radius p)) p)))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2)))))
                 (:instance point-in-r3 (x p))
                 (:instance normalize-dimensions-name (name '$arg) (l p))
                 (:instance normalize-dimensions-name (name '$arg)
                            (l (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2)))))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l p))
                 (:instance b3-0-set-a4-1-suff
                            (p-s2 (set-a-inv-r-a4-1-witness (b3-0-set-a-inv-r-a4-1-witness p)))
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2))
                                    p)))
                 (:instance r3-matrixp (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                0 (* 2 (acl2-pi))))
                                                            (point-on-s2-not-d))
                                               (a-rotation (acl2-sqrt 2)))))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (a-rotation (acl2-sqrt 2))))
                            (p2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                      0 (* 2 (acl2-pi))))
                                                  (point-on-s2-not-d))
                                     (a-rotation (acl2-sqrt 2))
                                     p)))
                 (:instance pr3-p=>pr3-a*p
                            (a (/ (cal-radius p)))
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2))
                                    p)))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-3
                            (wit-wit (set-a-inv-r-a4-1-witness (b3-0-set-a-inv-r-a4-1-witness p)))
                            (r-1-rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                           0 (* 2 (acl2-pi))))
                                                       (point-on-s2-not-d))
                                          (a-rotation (acl2-sqrt 2))))
                            (p p)
                            (a (/ (cal-radius p))))
                 (:instance associativity-of-m-*
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (a-rotation (acl2-sqrt 2)))
                            (m3 (s-* (/ (cal-radius p)) p)))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-4)
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-5
                            (a-1 (a-inv-rotation (acl2-sqrt 2)))
                            (a (a-rotation (acl2-sqrt 2)))
                            (a-1-2 (a-inv-rotation (acl2-sqrt 2)))
                            (id-1 (id-rotation))
                            (id-2 (id-rotation))
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-6)
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 )
           :in-theory nil
           )))

(defthmd b3-0-a-1-r-b3-0-a4-iff-b3-0-a-1-r-a4
  (iff (b3-0-a-inv-r-b3-0-set-a4 p)
       (b3-0-set-a-inv-r-a4 p))
  :hints (("goal"
           :use ((:instance b3-0-a-1-r-b3-0-a4=>b3-0-a-1-r-a4)
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4))
           )))

(defun-sk b3-0-r-1-a-inv-b3-0-set-a5-1 (p)
  (exists p-s2
          (and (b3-0-set-a5 p-s2)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                         (a-inv-rotation (acl2-sqrt 2))
                         p-s2)
                    p))))

(defun b3-0-r-1-a-inv-b3-0-set-a5 (p)
  (and (point-in-r3 p)
       (b3-0-r-1-a-inv-b3-0-set-a5-1 p)))


(defun-sk b3-0-set-r-1-a-inv-a5-1 (p)
  (exists p-s2
          (and (set-r-1-a-inv-a5 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-r-1-a-inv-a5 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-r-1-a-inv-a5-1 p)))

(defthmd b3-0-r-1-a-inv-b3-0-a5=>b3-0-r-1-a-1-a5
  (implies (b3-0-r-1-a-inv-b3-0-set-a5 p)
           (b3-0-set-r-1-a-inv-a5 p))
  :hints (("goal"
           :use ((:instance b3-0-r-1-a-inv-b3-0-set-a5 (p p))
                 (:instance b3-0-r-1-a-inv-b3-0-set-a5-1 (p p))
                 (:instance b3-0-set-a5 (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance b3-0-set-a5-1 (p (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance b3-0-set-r-1-a-inv-a5 (p p))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*rot-is-rot
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance b3-0-set-r-1-a-inv-a5-1-suff
                            (p-s2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                       (a-inv-rotation (acl2-sqrt 2))
                                       (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                            (p p))
                 (:instance set-r-1-a-inv-a5
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (a-inv-rotation (acl2-sqrt 2))
                                    (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))))
                 (:instance set-a5 (p (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                 (:instance wa-01 (p (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                 (:instance wa-0 (p (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                 (:instance s2-not-e (point (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                 (:instance s2-def-p (point (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))
                            (p2 p)
                            (rot (m-* (rotation-3d
                                       (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                       (point-on-s2-not-d))
                                      (a-inv-rotation (acl2-sqrt 2)))))
                 (:instance associativity-of-m-*
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m3 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                      (a-inv-rotation (acl2-sqrt 2)))))
                 (:instance r3-rotationp
                            (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (a-inv-rotation (acl2-sqrt 2)))))
                 (:instance associativity-of-m-*
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m3 (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                 (:instance set-r-1-a-inv-a5-1-suff
                            (p (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                            (point (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                        (a-inv-rotation (acl2-sqrt 2))
                                        (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))))
                 (:instance xyz-p1=xyz-p2
                            (p1 p)
                            (p2 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))
                            (p3 (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) (a-inv-rotation (acl2-sqrt 2))))
                            (a (/ (cal-radius p))))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p2 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))
                            (p1 (b3-0-set-a5-1-witness (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p)))
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 (b3-0-r-1-a-inv-b3-0-set-a5-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 )
           :in-theory nil
           )))

(defthmd b3-0-r-1-a-1-a5=>b3-0-r-1-a-inv-b3-0-a5
  (implies (b3-0-set-r-1-a-inv-a5 p)
           (b3-0-r-1-a-inv-b3-0-set-a5 p))
  :hints (("goal"
           :use ((:instance b3-0-set-r-1-a-inv-a5 (p p))
                 (:instance b3-0-set-r-1-a-inv-a5-1 (p p))
                 (:instance set-r-1-a-inv-a5 (p (b3-0-set-r-1-a-inv-a5-1-witness p)))
                 (:instance set-r-1-a-inv-a5-1 (point (b3-0-set-r-1-a-inv-a5-1-witness p)))
                 (:instance b3-0-r-1-a-inv-b3-0-set-a5 (p p))
                 (:instance b3-0-r-1-a-inv-b3-0-set-a5-1-suff
                            (p p)
                            (p-s2 (m-* (a-rotation (acl2-sqrt 2))
                                       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                       p)))
                 (:instance b3-0-set-a5 (p (m-* (a-rotation (acl2-sqrt 2))
                                                (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                                p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot (m-* (a-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*rot-is-rot
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance r3-rotationp (m (m-* (a-rotation (acl2-sqrt 2))
                                                 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance associativity-of-m-*
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m3 p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-r-1-a-inv-a5-1-witness p))
                            (p2 p)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 (:instance set-a5 (p (set-r-1-a-inv-a5-1-witness
                                       (b3-0-set-r-1-a-inv-a5-1-witness p))))
                 (:instance wa-01 (p (set-r-1-a-inv-a5-1-witness
                                      (b3-0-set-r-1-a-inv-a5-1-witness p))))
                 (:instance wa-0 (p (set-r-1-a-inv-a5-1-witness (b3-0-set-r-1-a-inv-a5-1-witness p))))
                 (:instance s2-not-e (point (set-r-1-a-inv-a5-1-witness (b3-0-set-r-1-a-inv-a5-1-witness p))))
                 (:instance s2-def-p (point (set-r-1-a-inv-a5-1-witness (b3-0-set-r-1-a-inv-a5-1-witness p))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-1
                            (r (a-inv-rotation (acl2-sqrt 2)))
                            (a (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (wit-wit (set-r-1-a-inv-a5-1-witness (b3-0-set-r-1-a-inv-a5-1-witness p)))
                            (wit-wit-1 (set-r-1-a-inv-a5-1-witness (b3-0-set-r-1-a-inv-a5-1-witness p)))
                            (wit (b3-0-set-r-1-a-inv-a5-1-witness p))
                            (r-1 (a-rotation (acl2-sqrt 2)))
                            (id-1 (id-rotation))
                            (r1 (a-inv-rotation (acl2-sqrt 2)))
                            (a-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (id-2 (id-rotation)))
                 (:instance m-*point-id=point
                            (p1 (set-r-1-a-inv-a5-1-witness (b3-0-set-r-1-a-inv-a5-1-witness p))))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp (m (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance m*id=m (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-2
                            (wit-wit (set-r-1-a-inv-a5-1-witness (b3-0-set-r-1-a-inv-a5-1-witness p)))
                            (wit (b3-0-set-r-1-a-inv-a5-1-witness p))
                            (a (a-rotation (acl2-sqrt 2)))
                            (b (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (s (s-* (/ (cal-radius p)) p)))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (m-* (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance point-in-r3 (x p))
                 (:instance normalize-dimensions-name (name '$arg) (l p))
                 (:instance normalize-dimensions-name (name '$arg)
                            (l (m-* (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l p))
                 (:instance b3-0-set-a5-1-suff
                            (p-s2 (set-r-1-a-inv-a5-1-witness (b3-0-set-r-1-a-inv-a5-1-witness p)))
                            (p (m-* (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                    p)))
                 (:instance r3-matrixp (m (m-* (a-rotation (acl2-sqrt 2))
                                               (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (rot (m-* (a-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                            (p2 (m-* (a-rotation (acl2-sqrt 2))
                                     (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                     p)))
                 (:instance pr3-p=>pr3-a*p
                            (a (/ (cal-radius p)))
                            (p (m-* (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d))
                                    p)))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-3
                            (wit-wit (set-r-1-a-inv-a5-1-witness (b3-0-set-r-1-a-inv-a5-1-witness p)))
                            (r-1-rot (m-* (a-rotation (acl2-sqrt 2))
                                          (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                            (p p)
                            (a (/ (cal-radius p))))
                 (:instance associativity-of-m-*
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m1 (a-rotation (acl2-sqrt 2)))
                            (m3 (s-* (/ (cal-radius p)) p)))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-4)
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-5
                            (r (a-inv-rotation (acl2-sqrt 2)))
                            (r-1 (a-rotation (acl2-sqrt 2)))
                            (a-1-2 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi))))
                                                (point-on-s2-not-d)))
                            (id-1 (id-rotation))
                            (id-2 (id-rotation))
                            (a (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (a-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-6)
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 )
           :in-theory nil
           )))

(defthmd b3-0-r-1-a-inv-b3-0-a5-iff-b3-0-r-1-a-1-a5
  (iff (b3-0-r-1-a-inv-b3-0-set-a5 p)
       (b3-0-set-r-1-a-inv-a5 p))
  :hints (("goal"
           :use ((:instance b3-0-r-1-a-inv-b3-0-a5=>b3-0-r-1-a-1-a5)
                 (:instance b3-0-r-1-a-1-a5=>b3-0-r-1-a-inv-b3-0-a5))
           :in-theory (disable (:executable-counterpart tau-system))
           )))

(defun-sk b3-0-r-1-a-inv-r-b3-0-set-a6-1 (p)
  (exists p-s2
          (and (b3-0-set-a6 p-s2)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                         (a-inv-rotation (acl2-sqrt 2))
                         (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                         p-s2)
                    p))))

(defun b3-0-r-1-a-inv-r-b3-0-set-a6 (p)
  (and (point-in-r3 p)
       (b3-0-r-1-a-inv-r-b3-0-set-a6-1 p)))


(defun-sk b3-0-set-r-1-a-inv-r-a6-1 (p)
  (exists p-s2
          (and (set-r-1-a-inv-r-a6 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-r-1-a-inv-r-a6 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-r-1-a-inv-r-a6-1 p)))

(defthmd b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
  (implies (and (r3-rotationp m1)
                (r3-rotationp m2)
                (r3-rotationp m3))
           (r3-rotationp (m-* m1 m2 m3)))
  :hints (("goal"
           :use ((:instance rot*rot-is-rot
                            (m1 (m-* m1 m2))
                            (m2 m3))
                 )
           :in-theory (disable r3-rotationp (:executable-counterpart tau-system))
           )))

(defthmd b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-2
  (equal (m-* (m-* m1 m2 m3) m4) (m-* m1 m2 m3 m4)))

(defthmd b3-0-r-1-a-inv-r-b3-0-a6=>b3-0-r-1-a-1-r-a6
  (implies (b3-0-r-1-a-inv-r-b3-0-set-a6 p)
           (b3-0-set-r-1-a-inv-r-a6 p))
  :hints (("goal"
           :use ((:instance b3-0-r-1-a-inv-r-b3-0-set-a6 (p p))
                 (:instance b3-0-r-1-a-inv-r-b3-0-set-a6-1 (p p))
                 (:instance b3-0-set-a6 (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance b3-0-set-a6-1 (p (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance b3-0-set-r-1-a-inv-r-a6 (p p))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))
                            (p2 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (a-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi)))
                                                   (point-on-s2-not-d)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-2
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m4 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                 (:instance b3-0-set-r-1-a-inv-r-a6-1-suff
                            (p p)
                            (p-s2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                       (a-inv-rotation (acl2-sqrt 2))
                                       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                       (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))))
                 (:instance set-r-1-a-inv-r-a6
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (a-inv-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                    (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))))
                 (:instance set-a6
                            (p (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))))
                 (:instance set-a6-1
                            (point (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))))
                 (:instance wa-11
                            (p (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))))
                 (:instance wa-1
                            (p (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))))
                 (:instance set-e-p
                            (point (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))))
                 (:instance set-r-1-a-inv-r-a6-1-suff
                            (p (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                            (point (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                        (a-inv-rotation (acl2-sqrt 2))
                                        (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                        (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))))
                 (:instance r3-rotationp
                            (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (a-inv-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                      (a-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-2
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (a-inv-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m4 (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))))
                 (:instance xyz-p1=xyz-p2
                            (p3 (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                            (p2 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))
                            (a (/ (cal-radius p)))
                            (p1 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                      (a-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-a6-1-witness (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p)))
                            (p2 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 (b3-0-r-1-a-inv-r-b3-0-set-a6-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 )
           :in-theory nil
           ))
  )

(defthmd b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6-1
  (implies (and (m-= (m-* r-1 a-1 r wit-wit) wit)
                (m-= (m-* r r-1) id-1)
                (m-= (m-* id-1 a-1) a-1-1)
                (m-= (m-* a a-1-1) id-2)
                (m-= (m-* id-2 r) r1)
                (m-= (m-* r-1 r1) id-3)
                (m-= (m-* id-3 wit-wit) wit-wit-1))
           (m-= wit-wit-1 (m-* r-1 a r wit))))

(defthmd b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6-2
  (implies (and (m-= wit-wit (m-* m1 m2 m3 wit))
                (m-= wit s))
           (m-= wit-wit (m-* m1 m2 m3 s))))

(defthmd b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6-3
  (implies (and (m-= (m-* r r-1) id-1)
                (m-= (m-* id-1 a) a1)
                (m-= (m-* a-1 a1) id-2)
                (m-= (m-* id-2 r) r1)
                (m-= (m-* r-1 r1) id-3)
                (m-= (m-* id-3 p) p))
           (m-= (m-* r-1 a-1 r (m-* r-1 a r) p) p)))

(defthmd b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6
  (implies (b3-0-set-r-1-a-inv-r-a6 p)
           (b3-0-r-1-a-inv-r-b3-0-set-a6 p))
  :hints (("goal"
           :use ((:instance b3-0-set-r-1-a-inv-r-a6)
                 (:instance b3-0-set-r-1-a-inv-r-a6-1)
                 (:instance set-r-1-a-inv-r-a6 (p (b3-0-set-r-1-a-inv-r-a6-1-witness p)))
                 (:instance set-r-1-a-inv-r-a6-1 (point (b3-0-set-r-1-a-inv-r-a6-1-witness p)))
                 (:instance b3-0-r-1-a-inv-r-b3-0-set-a6 (p p))
                 (:instance b3-0-r-1-a-inv-r-b3-0-set-a6-1-suff
                            (p-s2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                        0 (* 2 (acl2-pi))))
                                                    (point-on-s2-not-d))
                                       (a-rotation (acl2-sqrt 2))
                                       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi)))
                                                    (point-on-s2-not-d))
                                       p))
                            (p p))
                 (:instance b3-0-set-a6 (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                 0 (* 2 (acl2-pi))))
                                                             (point-on-s2-not-d))
                                                (a-rotation (acl2-sqrt 2))
                                                (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                              0 (* 2 (acl2-pi)))
                                                             (point-on-s2-not-d))
                                                p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (a-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi)))
                                                   (point-on-s2-not-d)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (a-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp
                            (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-2
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (a-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m4 p))
                 (:instance b3-0-set-a6-1-suff
                            (p-s2 (set-r-1-a-inv-r-a6-1-witness (b3-0-set-r-1-a-inv-r-a6-1-witness p)))
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d))
                                    p)))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (a-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi)))
                                                   (point-on-s2-not-d))))
                            (p1 p)
                            (p2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                      0 (* 2 (acl2-pi))))
                                                  (point-on-s2-not-d))
                                     (a-rotation (acl2-sqrt 2))
                                     (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                   0 (* 2 (acl2-pi)))
                                                  (point-on-s2-not-d))
                                     p)))
                 (:instance b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6-1
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (a-1 (a-inv-rotation (acl2-sqrt 2)))
                            (r (rotation-3d
                                (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                (point-on-s2-not-d)))
                            (wit-wit (set-r-1-a-inv-r-a6-1-witness (b3-0-set-r-1-a-inv-r-a6-1-witness p)))
                            (wit (b3-0-set-r-1-a-inv-r-a6-1-witness p))
                            (id-1 (id-rotation))
                            (a-1-1 (a-inv-rotation (acl2-sqrt 2)))
                            (a (a-rotation (acl2-sqrt 2)))
                            (id-2 (id-rotation))
                            (r1 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (id-3 (id-rotation))
                            (wit-wit-1 (set-r-1-a-inv-r-a6-1-witness (b3-0-set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance m-*point-id=point
                            (p1 (set-r-1-a-inv-r-a6-1-witness (b3-0-set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance set-a6 (p (set-r-1-a-inv-r-a6-1-witness (b3-0-set-r-1-a-inv-r-a6-1-witness p))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-3
                            (wit-wit (set-r-1-a-inv-r-a6-1-witness (b3-0-set-r-1-a-inv-r-a6-1-witness p)))
                            (r-1-rot (m-*
                                      (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (a-rotation (acl2-sqrt 2))
                                      (rotation-3d
                                       (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                       (point-on-s2-not-d))))
                            (a (/ (cal-radius p)))
                            (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-r-1-a-inv-r-a6-1-witness p))
                            (p2 p)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 (:instance b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6-2
                            (wit-wit (set-r-1-a-inv-r-a6-1-witness (b3-0-set-r-1-a-inv-r-a6-1-witness p)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (a-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (wit (b3-0-set-r-1-a-inv-r-a6-1-witness p))
                            (s (s-* (/ (cal-radius p)) p)))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-2
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (a-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (m4 (s-* (/ (cal-radius p)) p)))
                 (:instance r3-matrixp
                            (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance pr3-p=>pr3-a*p
                            (a (/ (cal-radius p)))
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d))
                                    p)))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance normalize-dimensions-name (name '$arg) (l p))
                 (:instance normalize-dimensions-name (name '$arg)
                            (l (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (a-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance point-in-r3 (x p))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l p))
                 (:instance id*m=m (m1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance r3-rotationp (m (rotation-3d
                                             (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-6)
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-4)
                 (:instance b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6-3
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (r1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (id-1 (id-rotation))
                            (id-2 (id-rotation))
                            (id-3 (id-rotation))
                            (p p)
                            (a-1 (a-inv-rotation (acl2-sqrt 2)))
                            (a (a-rotation (acl2-sqrt 2)))
                            (a1 (a-rotation (acl2-sqrt 2))))
                 (:instance m-*point-id=point (p1 p))
                 )
           :in-theory nil
           )))

(defthmd b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6
  (iff (b3-0-set-r-1-a-inv-r-a6 p)
       (b3-0-r-1-a-inv-r-b3-0-set-a6 p))
  :hints (("goal"
           :use ((:instance b3-0-r-1-a-inv-r-b3-0-a6=>b3-0-r-1-a-1-r-a6)
                 (:instance b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6))
           :in-theory (disable (:executable-counterpart tau-system))
           )))

(defthmd b3-0=>a3-to-a8
  (implies (b3-0-s2 p)
           (or (b3-0-set-a-inv-a3 p)
               (b3-0-set-a-inv-r-a4 p)
               (b3-0-set-r-1-a-inv-a5 p)
               (b3-0-set-r-1-a-inv-r-a6 p)
               (b3-0-set-a7 p)
               (b3-0-set-a8 p)))
  :hints (("goal"
           :use ((:instance b3-0-s2 (p p))
                 (:instance b3-0-s2-1 (p p))
                 (:instance s2-equiv-2 (p (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a-inv-a3 (p p))
                 (:instance b3-0-set-a-inv-a3-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a-inv-r-a4 (p p))
                 (:instance b3-0-set-a-inv-r-a4-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-r-1-a-inv-a5 (p p))
                 (:instance b3-0-set-r-1-a-inv-a5-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-r-1-a-inv-r-a6 (p p))
                 (:instance b3-0-set-r-1-a-inv-r-a6-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a7 (p p))
                 (:instance b3-0-set-a7-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a8 (p p))
                 (:instance b3-0-set-a8-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd a3-to-a8=>b3-0
  (implies (or (b3-0-set-a-inv-a3 p)
               (b3-0-set-a-inv-r-a4 p)
               (b3-0-set-r-1-a-inv-a5 p)
               (b3-0-set-r-1-a-inv-r-a6 p)
               (b3-0-set-a7 p)
               (b3-0-set-a8 p))
           (b3-0 p))
  :hints (("goal"
           :in-theory (disable b3-0-set-a-inv-a3-1
                               b3-0-set-a-inv-r-a4-1
                               b3-0-set-r-1-a-inv-a5-1
                               b3-0-set-r-1-a-inv-r-a6-1
                               b3-0-set-a7-1
                               b3-0-set-a8-1)
           )))

(defthmd b3-0-iff-a3-to-a8-1
  (iff (or (b3-0-s2 p)
           (b3-0 p))
       ;; (or (or (b3-0-set-a-inv-a3 p)
       ;;         (b3-0-set-a-inv-r-a4 p)
       ;;         (b3-0-set-r-1-a-inv-a5 p)
       ;;         (b3-0-set-r-1-a-inv-r-a6 p)
       ;;         (b3-0-set-a7 p)
       ;;         (b3-0-set-a8 p))
       (or (b3-0-a-inv-b3-0-set-a3 p)
           (b3-0-a-inv-r-b3-0-set-a4 p)
           (b3-0-r-1-a-inv-b3-0-set-a5 p)
           (b3-0-r-1-a-inv-r-b3-0-set-a6 p)
           (b3-0-set-a7 p)
           (b3-0-set-a8 p)))
  :hints (("goal"
           :use ((:instance b3-0-iff-b3-0-s2 (p p))
                 (:instance b3-0=>a3-to-a8 (p p))
                 (:instance a3-to-a8=>b3-0 (p p))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6)
                 (:instance b3-0-r-1-a-inv-b3-0-a5-iff-b3-0-r-1-a-1-a5)
                 (:instance b3-0-a-1-r-b3-0-a4-iff-b3-0-a-1-r-a4)
                 (:instance b3-0-a-1-b3-0-a3-iff-b3-0-a-1-a3))
           :in-theory nil
           )))

(defun-sk b3-0-b-inv-b3-0-set-a9-1 (p)
  (exists p-s2
          (and (b3-0-set-a9 p-s2)
               (m-= (m-* (b-inv-rotation (acl2-sqrt 2)) p-s2)
                    p))))

(defun b3-0-b-inv-b3-0-set-a9 (p)
  (and (point-in-r3 p)
       (b3-0-b-inv-b3-0-set-a9-1 p)))

(defun-sk b3-0-set-b-inv-a9-1 (p)
  (exists p-s2
          (and (set-b-inv-a9 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-b-inv-a9 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-b-inv-a9-1 p)))

(defthmd b3-0-b-1-a9-iff-b-1-b3-0-a9-1
  (implies (and (equal (point-in-r3-x1
                        (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                       (* (point-in-r3-x1 (b3-0-b-inv-b3-0-set-a9-1-witness p))
                          (/ (cal-radius p))))
                (equal (point-in-r3-y1
                        (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                       (* (point-in-r3-y1 (b3-0-b-inv-b3-0-set-a9-1-witness p))
                          (/ (cal-radius p))))
                (equal (point-in-r3-z1
                        (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                       (* (point-in-r3-z1 (b3-0-b-inv-b3-0-set-a9-1-witness p))
                          (/ (cal-radius p)))))
           (and (equal (point-in-r3-x1
                        (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                       (* (/ (cal-radius p))
                          (point-in-r3-x1 (b3-0-b-inv-b3-0-set-a9-1-witness p))))
                (equal (point-in-r3-z1
                        (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                       (* (/ (cal-radius p))
                          (point-in-r3-z1 (b3-0-b-inv-b3-0-set-a9-1-witness p))))
                (equal (point-in-r3-y1
                        (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                       (* (/ (cal-radius p))
                          (point-in-r3-y1 (b3-0-b-inv-b3-0-set-a9-1-witness p)))))))

(defthmd b3-0-b-1-b3-0-a9=>b3-0-b-1-a9
  (implies (b3-0-b-inv-b3-0-set-a9 p)
           (b3-0-set-b-inv-a9 p))
  :hints (("goal"
           :use ((:instance b3-0-b-inv-b3-0-set-a9 (p p))
                 (:instance b3-0-b-inv-b3-0-set-a9-1 (p p))
                 (:instance b3-0-set-a9 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance b3-0-set-a9-1 (p (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                 (:instance b3-0-set-b-inv-a9 (p p))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2 (p1 (b3-0-b-inv-b3-0-set-a9-1-witness p))
                            (p2 p)
                            (rot (b-inv-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0-set-b-inv-a9-1-suff
                            (p-s2 (m-* (b-inv-rotation (acl2-sqrt 2))
                                       (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p))))
                            (p p))
                 (:instance set-b-inv-a9 (p (m-* (b-inv-rotation (acl2-sqrt 2))
                                                 (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))))
                 (:instance set-a9 (p (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p))))
                 (:instance wb-00 (p (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p))))
                 (:instance wb-0 (p (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p))))
                 (:instance s2-not-e (point (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p))))
                 (:instance s2-def-p (point (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                            (rot (b-inv-rotation (acl2-sqrt 2))))
                 (:instance r3-rotationp (m (b-inv-rotation (acl2-sqrt 2))))
                 (:instance set-b-inv-a9-1-suff
                            (p (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                            (point (m-* (b-inv-rotation (acl2-sqrt 2))
                                        (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))))
                 (:instance xyz-p1=xyz-p2
                            (p1 p)
                            (p2 (b3-0-b-inv-b3-0-set-a9-1-witness p))
                            (p3 (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                            (rot (b-inv-rotation (acl2-sqrt 2)))
                            (a (/ (cal-radius p))))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-a9-1-witness (b3-0-b-inv-b3-0-set-a9-1-witness p)))
                            (p2 (b3-0-b-inv-b3-0-set-a9-1-witness p))
                            (a (/ (cal-radius p))))
                 (:instance b3-0-b-1-a9-iff-b-1-b3-0-a9-1)
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 )
           :in-theory nil
           )))

(defthmd b3-0-b-1-a9=>b3-0-b-1-b3-0-a9-1
  (implies (point-in-r3 p1)
           (m-= (m-* (b-rotation (acl2-sqrt 2)) (b-inv-rotation (acl2-sqrt 2)) p1)
                p1))
  :hints (("goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance associativity-of-m-*
                            (m1 (b-rotation (acl2-sqrt 2)))
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m3 p1))
                 )
           :in-theory (e/d () (a-rotation a-inv-rotation b-rotation b-inv-rotation acl2-sqrt m-= m-* (:executable-counterpart id-rotation) id-rotation associativity-of-m-* m-*point-id=point))
           )))

(defthmd b3-0-b-1-a9=>b3-0-b-1-b3-0-a9-2
  (implies (and (equal
                 (point-in-r3-x1 (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p)))
                 (* (/ (cal-radius p))
                    (point-in-r3-x1 (m-* (b-rotation (acl2-sqrt 2)) p))))
                (equal
                 (point-in-r3-y1 (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p)))
                 (* (/ (cal-radius p))
                    (point-in-r3-y1 (m-* (b-rotation (acl2-sqrt 2)) p))))
                (equal
                 (point-in-r3-z1 (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p)))
                 (* (/ (cal-radius p))
                    (point-in-r3-z1 (m-* (b-rotation (acl2-sqrt 2)) p)))))
           (and (equal
                 (point-in-r3-x1 (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p)))
                 (* (point-in-r3-x1 (m-* (b-rotation (acl2-sqrt 2)) p))
                    (/ (cal-radius p))))
                (equal
                 (point-in-r3-y1 (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p)))
                 (* (point-in-r3-y1 (m-* (b-rotation (acl2-sqrt 2)) p))
                    (/ (cal-radius p))))
                (equal
                 (point-in-r3-z1 (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p)))
                 (* (point-in-r3-z1 (m-* (b-rotation (acl2-sqrt 2)) p))
                    (/ (cal-radius p)))))))

(defthmd b3-0-b-1-a9=>b3-0-b-1-b3-0-a9-3
  (implies (point-in-r3 p1)
           (m-= (m-* (b-inv-rotation (acl2-sqrt 2)) (b-rotation (acl2-sqrt 2)) p1)
                p1))
  :hints (("goal"
           :use ((:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p1))
                 (:instance associativity-of-m-*
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (b-rotation (acl2-sqrt 2)))
                            (m3 p1))
                 )
           :in-theory (e/d () (a-rotation a-inv-rotation b-rotation b-inv-rotation acl2-sqrt m-= m-* (:executable-counterpart id-rotation) id-rotation associativity-of-m-* m-*point-id=point))
           )))

(defthmd b3-0-b-1-a9=>b3-0-b-1-b3-0-a9
  (implies (b3-0-set-b-inv-a9 p)
           (b3-0-b-inv-b3-0-set-a9 p))
  :hints (("goal"
           :use ((:instance b3-0-set-b-inv-a9 (p p))
                 (:instance b3-0-set-b-inv-a9-1 (p p))
                 (:instance set-b-inv-a9 (p (b3-0-set-b-inv-a9-1-witness p)))
                 (:instance set-b-inv-a9-1 (point (b3-0-set-b-inv-a9-1-witness p)))
                 (:instance b3-0-b-inv-b3-0-set-a9 (p p))
                 (:instance b3-0-b-inv-b3-0-set-a9-1-suff
                            (p p)
                            (p-s2 (m-* (b-rotation (acl2-sqrt 2)) p)))
                 (:instance b3-0-set-a9 (p (m-* (b-rotation (acl2-sqrt 2)) p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot (b-rotation (acl2-sqrt 2))))
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp (m (b-rotation (acl2-sqrt 2))))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-b-inv-a9-1-witness p))
                            (p2 p)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 (:instance set-a9 (p (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                 (:instance wb-00 (p (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                 (:instance wb-0 (p (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                 (:instance s2-not-e (point (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                 (:instance s2-def-p (point (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                 (:instance m-=-implies-equal-m-*-2
                            (m1 (b-rotation (acl2-sqrt 2)))
                            (m2 (m-* (b-inv-rotation (acl2-sqrt 2))
                                     (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                            (m2-equiv (b3-0-set-b-inv-a9-1-witness p)))
                 (:instance b3-0-b-1-a9=>b3-0-b-1-b3-0-a9-1
                            (p1 (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                 (:instance m-*-s-*-right
                            (m1 (b-rotation (acl2-sqrt 2)))
                            (m2 p)
                            (name :fake-name)
                            (a (/ (cal-radius p))))
                 (:instance r3-matrixp (m (b-rotation (acl2-sqrt 2))))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (b-rotation (acl2-sqrt 2))))
                 (:instance point-in-r3 (x p))
                 (:instance normalize-dimensions-name (name '$arg) (l p))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l p))
                 (:instance m-=-implies-equal-m-*-2
                            (m1 (b-rotation (acl2-sqrt 2)))
                            (m2 (b3-0-set-b-inv-a9-1-witness p))
                            (m2-equiv (s-* (/ (cal-radius p)) p)))
                 (:instance b3-0-set-a9-1-suff
                            (p-s2 (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p)))
                            (p (m-* (b-rotation (acl2-sqrt 2)) p)))
                 (:instance m-=m1m2=>r-m1=r-m2-1
                            (p1 (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p)))
                            (p2 (s-* (/ (cal-radius p))
                                     (m-* (b-rotation (acl2-sqrt 2)) p))))
                 (:instance pr3-p=>pr3-a*p
                            (a (/ (cal-radius p)))
                            (p (m-* (b-rotation (acl2-sqrt 2)) p)))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (a (/ (cal-radius p)))
                            (m (m-* (b-rotation (acl2-sqrt 2)) p))
                            (i 0)
                            (j 0))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (a (/ (cal-radius p)))
                            (m (m-* (b-rotation (acl2-sqrt 2)) p))
                            (i 1)
                            (j 0))
                 (:instance aref2-s-*
                            (name :fake-name)
                            (a (/ (cal-radius p)))
                            (m (m-* (b-rotation (acl2-sqrt 2)) p))
                            (i 2)
                            (j 0))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (p2 (m-* (b-rotation (acl2-sqrt 2)) p))
                            (rot (b-rotation (acl2-sqrt 2))))
                 (:instance point-in-r3-x1
                            (p (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                 (:instance point-in-r3-x1
                            (p (m-* (b-rotation (acl2-sqrt 2)) p)))
                 (:instance point-in-r3-y1
                            (p (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                 (:instance point-in-r3-y1
                            (p (m-* (b-rotation (acl2-sqrt 2)) p)))
                 (:instance point-in-r3-z1
                            (p (set-b-inv-a9-1-witness (b3-0-set-b-inv-a9-1-witness p))))
                 (:instance point-in-r3-z1
                            (p (m-* (b-rotation (acl2-sqrt 2)) p)))
                 (:instance b3-0-b-1-a9=>b3-0-b-1-b3-0-a9-2)
                 (:instance b3-0-b-1-a9=>b3-0-b-1-b3-0-a9-3 (p1 p))
                 )
           :in-theory nil
           )))

(defthmd b3-0-b-1-b3-0-a9-iff-b3-0-b-1-a9
  (iff (b3-0-b-inv-b3-0-set-a9 p)
       (b3-0-set-b-inv-a9 p))
  :hints (("goal"
           :use ((:instance b3-0-b-1-b3-0-a9=>b3-0-b-1-a9)
                 (:instance b3-0-b-1-a9=>b3-0-b-1-b3-0-a9))
           :in-theory nil
           )))

(defun-sk b3-0-b-inv-r-b3-0-set-a10-1 (p)
  (exists p-s2
          (and (b3-0-set-a10 p-s2)
               (m-= (m-* (b-inv-rotation (acl2-sqrt 2))
                         (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                         p-s2)
                    p))))

(defun b3-0-b-inv-r-b3-0-set-a10 (p)
  (and (point-in-r3 p)
       (b3-0-b-inv-r-b3-0-set-a10-1 p)))


(defun-sk b3-0-set-b-inv-r-a10-1 (p)
  (exists p-s2
          (and (set-b-inv-r-a10 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-b-inv-r-a10 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-b-inv-r-a10-1 p)))

(defthmd b3-0-b-1-r-b3-0-a10=>b3-0-b-1-r-a10
  (implies (b3-0-b-inv-r-b3-0-set-a10 p)
           (b3-0-set-b-inv-r-a10 p))
  :hints (("goal"
           :use ((:instance b3-0-b-inv-r-b3-0-set-a10 (p p))
                 (:instance b3-0-b-inv-r-b3-0-set-a10-1 (p p))
                 (:instance b3-0-set-a10 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance b3-0-set-a10-1 (p (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance b3-0-set-b-inv-r-a10 (p p))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*rot-is-rot
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance b3-0-set-b-inv-r-a10-1-suff
                            (p-s2 (m-* (b-inv-rotation (acl2-sqrt 2))
                                       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                       (b3-0-set-a10-1-witness (b3-0-b-inv-r-b3-0-set-a10-1-witness p))))
                            (p p))
                 (:instance set-b-inv-r-a10
                            (p (m-* (b-inv-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                    (b3-0-set-a10-1-witness (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))))
                 (:instance set-a10 (p (b3-0-set-a10-1-witness (b3-0-b-inv-r-b3-0-set-a10-1-witness p))))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 (b3-0-b-inv-r-b3-0-set-a10-1-witness p))
                            (p2 p)
                            (rot (m-* (b-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d
                                       (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                       (point-on-s2-not-d)))))
                 (:instance associativity-of-m-*
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m3 (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b3-0-set-a10-1-witness (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                            (rot (m-* (b-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance r3-rotationp
                            (m (m-* (b-inv-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance associativity-of-m-*
                            (m1 (b-inv-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m3 (b3-0-set-a10-1-witness (b3-0-b-inv-r-b3-0-set-a10-1-witness p))))
                 (:instance set-b-inv-r-a10-1-suff
                            (p (b3-0-set-a10-1-witness (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                            (point (m-* (b-inv-rotation (acl2-sqrt 2))
                                        (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                        (b3-0-set-a10-1-witness (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))))
                 (:instance xyz-p1=xyz-p2
                            (p1 p)
                            (p2 (b3-0-b-inv-r-b3-0-set-a10-1-witness p))
                            (p3 (b3-0-set-a10-1-witness (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                            (rot (m-* (b-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi)))
                                                   (point-on-s2-not-d))))
                            (a (/ (cal-radius p))))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-a10-1-witness (b3-0-b-inv-r-b3-0-set-a10-1-witness p)))
                            (p2 (b3-0-b-inv-r-b3-0-set-a10-1-witness p))
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 (b3-0-b-inv-r-b3-0-set-a10-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 (b3-0-b-inv-r-b3-0-set-a10-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 (b3-0-b-inv-r-b3-0-set-a10-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 )
           :in-theory nil
           )))

(defthmd b3-0-b-1-r-a10=>b3-0-b-1-r-b3-0-a10
  (implies (b3-0-set-b-inv-r-a10 p)
           (b3-0-b-inv-r-b3-0-set-a10 p))
  :hints (("goal"
           :use ((:instance b3-0-set-b-inv-r-a10 (p p))
                 (:instance b3-0-set-b-inv-r-a10-1 (p p))
                 (:instance set-b-inv-r-a10 (p (b3-0-set-b-inv-r-a10-1-witness p)))
                 (:instance set-b-inv-r-a10-1 (point (b3-0-set-b-inv-r-a10-1-witness p)))
                 (:instance b3-0-b-inv-r-b3-0-set-a10 (p p))
                 (:instance b3-0-b-inv-r-b3-0-set-a10-1-suff
                            (p p)
                            (p-s2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                       (b-rotation (acl2-sqrt 2)) p)))
                 (:instance b3-0-set-a10 (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                  0 (* 2 (acl2-pi))))
                                                              (point-on-s2-not-d))
                                                 (b-rotation (acl2-sqrt 2))
                                                 p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (b-rotation (acl2-sqrt 2)))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*rot-is-rot
                            (m2 (b-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance r3-rotationp (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                  0 (* 2 (acl2-pi))))
                                                              (point-on-s2-not-d))
                                                 (b-rotation (acl2-sqrt 2)))))
                 (:instance associativity-of-m-*
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (b-rotation (acl2-sqrt 2)))
                            (m3 p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-b-inv-r-a10-1-witness p))
                            (p2 p)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 (:instance set-a10 (p (set-b-inv-r-a10-1-witness (b3-0-set-b-inv-r-a10-1-witness p))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-1
                            (a-1 (b-inv-rotation (acl2-sqrt 2)))
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (wit-wit (set-b-inv-r-a10-1-witness (b3-0-set-b-inv-r-a10-1-witness p)))
                            (wit-wit-1 (set-b-inv-r-a10-1-witness (b3-0-set-b-inv-r-a10-1-witness p)))
                            (wit (b3-0-set-b-inv-r-a10-1-witness p))
                            (a (b-rotation (acl2-sqrt 2)))
                            (id-1 (id-rotation))
                            (r1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (id-2 (id-rotation)))
                 (:instance m-*point-id=point
                            (p1 (set-b-inv-r-a10-1-witness (b3-0-set-b-inv-r-a10-1-witness p))))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness
                                    0 (* 2 (acl2-pi)))))
                 (:instance r3-rotationp (m (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance id*m=m (m1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance m-*-s-*-right (m1 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                    0 (* 2 (acl2-pi))))
                                                                (point-on-s2-not-d))
                                                   (b-rotation (acl2-sqrt 2))))
                            (m2 p)
                            (name :fake-name)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-2
                            (wit-wit (set-b-inv-r-a10-1-witness (b3-0-set-b-inv-r-a10-1-witness p)))
                            (wit (b3-0-set-b-inv-r-a10-1-witness p))
                            (b (b-rotation (acl2-sqrt 2)))
                            (a (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                0 (* 2 (acl2-pi))))
                                            (point-on-s2-not-d)))
                            (s (s-* (/ (cal-radius p)) p)))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2)))))
                 (:instance point-in-r3 (x p))
                 (:instance normalize-dimensions-name (name '$arg) (l p))
                 (:instance normalize-dimensions-name (name '$arg)
                            (l (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2)))))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l p))
                 (:instance b3-0-set-a10-1-suff
                            (p-s2 (set-b-inv-r-a10-1-witness (b3-0-set-b-inv-r-a10-1-witness p)))
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2))
                                    p)))
                 (:instance r3-matrixp (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                0 (* 2 (acl2-pi))))
                                                            (point-on-s2-not-d))
                                               (b-rotation (acl2-sqrt 2)))))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (b-rotation (acl2-sqrt 2))))
                            (p2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                      0 (* 2 (acl2-pi))))
                                                  (point-on-s2-not-d))
                                     (b-rotation (acl2-sqrt 2))
                                     p)))
                 (:instance pr3-p=>pr3-a*p
                            (a (/ (cal-radius p)))
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2))
                                    p)))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-3
                            (wit-wit (set-b-inv-r-a10-1-witness (b3-0-set-b-inv-r-a10-1-witness p)))
                            (r-1-rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                           0 (* 2 (acl2-pi))))
                                                       (point-on-s2-not-d))
                                          (b-rotation (acl2-sqrt 2))))
                            (p p)
                            (a (/ (cal-radius p))))
                 (:instance associativity-of-m-*
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (b-rotation (acl2-sqrt 2)))
                            (m3 (s-* (/ (cal-radius p)) p)))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-4)
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-5
                            (a-1 (b-inv-rotation (acl2-sqrt 2)))
                            (a (b-rotation (acl2-sqrt 2)))
                            (a-1-2 (b-inv-rotation (acl2-sqrt 2)))
                            (id-1 (id-rotation))
                            (id-2 (id-rotation))
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-6)
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 )
           :in-theory nil
           )))

(defthmd b3-0-b-1-r-b3-0-a10-iff-b3-0-b-1-r-a10
  (iff (b3-0-b-inv-r-b3-0-set-a10 p)
       (b3-0-set-b-inv-r-a10 p))
  :hints (("goal"
           :use ((:instance b3-0-b-1-r-b3-0-a10=>b3-0-b-1-r-a10)
                 (:instance b3-0-b-1-r-a10=>b3-0-b-1-r-b3-0-a10))
           :in-theory nil
           )))

(defun-sk b3-0-r-1-b-inv-b3-0-set-a11-1 (p)
  (exists p-s2
          (and (b3-0-set-a11 p-s2)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                         (b-inv-rotation (acl2-sqrt 2))
                         p-s2)
                    p))))

(defun b3-0-r-1-b-inv-b3-0-set-a11 (p)
  (and (point-in-r3 p)
       (b3-0-r-1-b-inv-b3-0-set-a11-1 p)))


(defun-sk b3-0-set-r-1-b-inv-a11-1 (p)
  (exists p-s2
          (and (set-r-1-b-inv-a11 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-r-1-b-inv-a11 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-r-1-b-inv-a11-1 p)))

(defthmd b3-0-r-1-b-inv-b3-0-a11=>b3-0-r-1-b-1-a11
  (implies (b3-0-r-1-b-inv-b3-0-set-a11 p)
           (b3-0-set-r-1-b-inv-a11 p))
  :hints (("goal"
           :use ((:instance b3-0-r-1-b-inv-b3-0-set-a11 (p p))
                 (:instance b3-0-r-1-b-inv-b3-0-set-a11-1 (p p))
                 (:instance b3-0-set-a11 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance b3-0-set-a11-1 (p (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance b3-0-set-r-1-b-inv-a11 (p p))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*rot-is-rot
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance b3-0-set-r-1-b-inv-a11-1-suff
                            (p-s2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                       (b-inv-rotation (acl2-sqrt 2))
                                       (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                            (p p))
                 (:instance set-r-1-b-inv-a11
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (b-inv-rotation (acl2-sqrt 2))
                                    (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))))
                 (:instance set-a11 (p (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                 (:instance wb-01 (p (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                 (:instance wb-0 (p (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                 (:instance s2-not-e (point (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                 (:instance s2-def-p (point (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))
                            (p2 p)
                            (rot (m-* (rotation-3d
                                       (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))))
                                       (point-on-s2-not-d))
                                      (b-inv-rotation (acl2-sqrt 2)))))
                 (:instance associativity-of-m-*
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m3 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                      (b-inv-rotation (acl2-sqrt 2)))))
                 (:instance r3-rotationp
                            (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (b-inv-rotation (acl2-sqrt 2)))))
                 (:instance associativity-of-m-*
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m3 (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                 (:instance set-r-1-b-inv-a11-1-suff
                            (p (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                            (point (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                        (b-inv-rotation (acl2-sqrt 2))
                                        (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))))
                 (:instance xyz-p1=xyz-p2
                            (p1 p)
                            (p2 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))
                            (p3 (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d)) (b-inv-rotation (acl2-sqrt 2))))
                            (a (/ (cal-radius p))))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p2 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))
                            (p1 (b3-0-set-a11-1-witness (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p)))
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 (b3-0-r-1-b-inv-b3-0-set-a11-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 )
           :in-theory nil
           )))

(defthmd b3-0-r-1-b-1-a11=>b3-0-r-1-b-inv-b3-0-a11
  (implies (b3-0-set-r-1-b-inv-a11 p)
           (b3-0-r-1-b-inv-b3-0-set-a11 p))
  :hints (("goal"
           :use ((:instance b3-0-set-r-1-b-inv-a11 (p p))
                 (:instance b3-0-set-r-1-b-inv-a11-1 (p p))
                 (:instance set-r-1-b-inv-a11 (p (b3-0-set-r-1-b-inv-a11-1-witness p)))
                 (:instance set-r-1-b-inv-a11-1 (point (b3-0-set-r-1-b-inv-a11-1-witness p)))
                 (:instance b3-0-r-1-b-inv-b3-0-set-a11 (p p))
                 (:instance b3-0-r-1-b-inv-b3-0-set-a11-1-suff
                            (p p)
                            (p-s2 (m-* (b-rotation (acl2-sqrt 2))
                                       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                       p)))
                 (:instance b3-0-set-a11 (p (m-* (b-rotation (acl2-sqrt 2))
                                                 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                                 p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot (m-* (b-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance rot*rot-is-rot
                            (m1 (b-rotation (acl2-sqrt 2)))
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance r3-rotationp (m (m-* (b-rotation (acl2-sqrt 2))
                                                 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance associativity-of-m-*
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m1 (b-rotation (acl2-sqrt 2)))
                            (m3 p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-r-1-b-inv-a11-1-witness p))
                            (p2 p)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 (:instance set-a11 (p (set-r-1-b-inv-a11-1-witness
                                        (b3-0-set-r-1-b-inv-a11-1-witness p))))
                 (:instance wb-01 (p (set-r-1-b-inv-a11-1-witness
                                      (b3-0-set-r-1-b-inv-a11-1-witness p))))
                 (:instance wb-0 (p (set-r-1-b-inv-a11-1-witness (b3-0-set-r-1-b-inv-a11-1-witness p))))
                 (:instance s2-not-e (point (set-r-1-b-inv-a11-1-witness (b3-0-set-r-1-b-inv-a11-1-witness p))))
                 (:instance s2-def-p (point (set-r-1-b-inv-a11-1-witness (b3-0-set-r-1-b-inv-a11-1-witness p))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-1
                            (r (b-inv-rotation (acl2-sqrt 2)))
                            (a (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (wit-wit (set-r-1-b-inv-a11-1-witness (b3-0-set-r-1-b-inv-a11-1-witness p)))
                            (wit-wit-1 (set-r-1-b-inv-a11-1-witness (b3-0-set-r-1-b-inv-a11-1-witness p)))
                            (wit (b3-0-set-r-1-b-inv-a11-1-witness p))
                            (r-1 (b-rotation (acl2-sqrt 2)))
                            (id-1 (id-rotation))
                            (r1 (b-inv-rotation (acl2-sqrt 2)))
                            (a-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (id-2 (id-rotation)))
                 (:instance m-*point-id=point
                            (p1 (set-r-1-b-inv-a11-1-witness (b3-0-set-r-1-b-inv-a11-1-witness p))))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp (m (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance m*id=m (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-2
                            (wit-wit (set-r-1-b-inv-a11-1-witness (b3-0-set-r-1-b-inv-a11-1-witness p)))
                            (wit (b3-0-set-r-1-b-inv-a11-1-witness p))
                            (a (b-rotation (acl2-sqrt 2)))
                            (b (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (s (s-* (/ (cal-radius p)) p)))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (m-* (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance point-in-r3 (x p))
                 (:instance normalize-dimensions-name (name '$arg) (l p))
                 (:instance normalize-dimensions-name (name '$arg)
                            (l (m-* (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l p))
                 (:instance b3-0-set-a11-1-suff
                            (p-s2 (set-r-1-b-inv-a11-1-witness (b3-0-set-r-1-b-inv-a11-1-witness p)))
                            (p (m-* (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                    p)))
                 (:instance r3-matrixp (m (m-* (b-rotation (acl2-sqrt 2))
                                               (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 p)
                            (rot (m-* (b-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                            (p2 (m-* (b-rotation (acl2-sqrt 2))
                                     (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                     p)))
                 (:instance pr3-p=>pr3-a*p
                            (a (/ (cal-radius p)))
                            (p (m-* (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d))
                                    p)))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-3
                            (wit-wit (set-r-1-b-inv-a11-1-witness (b3-0-set-r-1-b-inv-a11-1-witness p)))
                            (r-1-rot (m-* (b-rotation (acl2-sqrt 2))
                                          (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                            (p p)
                            (a (/ (cal-radius p))))
                 (:instance associativity-of-m-*
                            (m2 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m1 (b-rotation (acl2-sqrt 2)))
                            (m3 (s-* (/ (cal-radius p)) p)))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-4)
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-5
                            (r (b-inv-rotation (acl2-sqrt 2)))
                            (r-1 (b-rotation (acl2-sqrt 2)))
                            (a-1-2 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi))))
                                                (point-on-s2-not-d)))
                            (id-1 (id-rotation))
                            (id-2 (id-rotation))
                            (a (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (a-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-6)
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance m-*point-id=point (p1 p))
                 )
           :in-theory nil
           )))

(defthmd b3-0-r-1-b-inv-b3-0-a11-iff-b3-0-r-1-b-1-a11
  (iff (b3-0-r-1-b-inv-b3-0-set-a11 p)
       (b3-0-set-r-1-b-inv-a11 p))
  :hints (("goal"
           :use ((:instance b3-0-r-1-b-inv-b3-0-a11=>b3-0-r-1-b-1-a11)
                 (:instance b3-0-r-1-b-1-a11=>b3-0-r-1-b-inv-b3-0-a11))
           :in-theory (disable (:executable-counterpart tau-system))
           )))

(defun-sk b3-0-r-1-b-inv-r-b3-0-set-a12-1 (p)
  (exists p-s2
          (and (b3-0-set-a12 p-s2)
               (m-= (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                         (b-inv-rotation (acl2-sqrt 2))
                         (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                         p-s2)
                    p))))

(defun b3-0-r-1-b-inv-r-b3-0-set-a12 (p)
  (and (point-in-r3 p)
       (b3-0-r-1-b-inv-r-b3-0-set-a12-1 p)))


(defun-sk b3-0-set-r-1-b-inv-r-a12-1 (p)
  (exists p-s2
          (and (set-r-1-b-inv-r-a12 p-s2)
               (equal (point-in-r3-x1 p-s2) (/ (point-in-r3-x1 p) (cal-radius p)))
               (equal (point-in-r3-y1 p-s2) (/ (point-in-r3-y1 p) (cal-radius p)))
               (equal (point-in-r3-z1 p-s2) (/ (point-in-r3-z1 p) (cal-radius p))))))

(defun b3-0-set-r-1-b-inv-r-a12 (p)
  (and (point-in-r3 p)
       (> (cal-radius p) 0)
       (<= (cal-radius p) 1)
       (b3-0-set-r-1-b-inv-r-a12-1 p)))

(defthmd b3-0-r-1-b-inv-r-b3-0-a12=>b3-0-r-1-b-1-r-a12
  (implies (b3-0-r-1-b-inv-r-b3-0-set-a12 p)
           (b3-0-set-r-1-b-inv-r-a12 p))
  :hints (("goal"
           :use ((:instance b3-0-r-1-b-inv-r-b3-0-set-a12 (p p))
                 (:instance b3-0-r-1-b-inv-r-b3-0-set-a12-1 (p p))
                 (:instance b3-0-set-a12 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance b3-0-set-a12-1 (p (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance b3-0-set-r-1-b-inv-r-a12 (p p))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (p1 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))
                            (p2 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (b-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi)))
                                                   (point-on-s2-not-d)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-2
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m4 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                 (:instance b3-0-set-r-1-b-inv-r-a12-1-suff
                            (p p)
                            (p-s2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                       (b-inv-rotation (acl2-sqrt 2))
                                       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                       (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))))
                 (:instance set-r-1-b-inv-r-a12
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (b-inv-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                    (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))))
                 (:instance set-a12
                            (p (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))))
                 (:instance set-a12-1
                            (point (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))))
                 (:instance wb-11
                            (p (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))))
                 (:instance wb-1
                            (p (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))))
                 (:instance set-e-p
                            (point (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))))
                 (:instance set-r-1-b-inv-r-a12-1-suff
                            (p (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                            (point (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                        (b-inv-rotation (acl2-sqrt 2))
                                        (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))
                                        (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))))
                 (:instance r3-rotationp
                            (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                    (b-inv-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                      (b-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-2
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (b-inv-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m4 (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))))
                 (:instance xyz-p1=xyz-p2
                            (p3 (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                            (p2 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))
                            (a (/ (cal-radius p)))
                            (p1 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))) (point-on-s2-not-d))
                                      (b-inv-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d)))))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-a12-1-witness (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p)))
                            (p2 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 (b3-0-r-1-b-inv-r-b3-0-set-a12-1-witness p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 )
           :in-theory nil
           ))
  )

(defthmd b3-0-r-1-b-1-r-a12=>b3-0-r-1-b-inv-r-b3-0-a12
  (implies (b3-0-set-r-1-b-inv-r-a12 p)
           (b3-0-r-1-b-inv-r-b3-0-set-a12 p))
  :hints (("goal"
           :use ((:instance b3-0-set-r-1-b-inv-r-a12)
                 (:instance b3-0-set-r-1-b-inv-r-a12-1)
                 (:instance set-r-1-b-inv-r-a12 (p (b3-0-set-r-1-b-inv-r-a12-1-witness p)))
                 (:instance set-r-1-b-inv-r-a12-1 (point (b3-0-set-r-1-b-inv-r-a12-1-witness p)))
                 (:instance b3-0-r-1-b-inv-r-b3-0-set-a12 (p p))
                 (:instance b3-0-r-1-b-inv-r-b3-0-set-a12-1-suff
                            (p-s2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                        0 (* 2 (acl2-pi))))
                                                    (point-on-s2-not-d))
                                       (b-rotation (acl2-sqrt 2))
                                       (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi)))
                                                    (point-on-s2-not-d))
                                       p))
                            (p p))
                 (:instance b3-0-set-a12 (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                                  0 (* 2 (acl2-pi))))
                                                              (point-on-s2-not-d))
                                                 (b-rotation (acl2-sqrt 2))
                                                 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                               0 (* 2 (acl2-pi)))
                                                              (point-on-s2-not-d))
                                                 p)))
                 (:instance set-e-p-iff-wit-inv*s2-d-p-n-set-e-p-1-1
                            (p1 p)
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (b-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi)))
                                                   (point-on-s2-not-d)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-1
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (b-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance r3-rotationp-r-theta
                            (angle (- (exists-in-interval-but-not-in-angle-sequence-witness
                                       0 (* 2 (acl2-pi))))))
                 (:instance r3-rotationp-r-theta
                            (angle (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))))
                 (:instance witness-not-in-angle-sequence)
                 (:instance base-rotations (x (acl2-sqrt 2)))
                 (:instance r3-rotationp
                            (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-2
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (b-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (m4 p))
                 (:instance b3-0-set-a12-1-suff
                            (p-s2 (set-r-1-b-inv-r-a12-1-witness (b3-0-set-r-1-b-inv-r-a12-1-witness p)))
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d))
                                    p)))
                 (:instance m-=m-*rot-p1=p2=>r-p1=r-p2
                            (rot (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (b-rotation (acl2-sqrt 2))
                                      (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                    0 (* 2 (acl2-pi)))
                                                   (point-on-s2-not-d))))
                            (p1 p)
                            (p2 (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                      0 (* 2 (acl2-pi))))
                                                  (point-on-s2-not-d))
                                     (b-rotation (acl2-sqrt 2))
                                     (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                   0 (* 2 (acl2-pi)))
                                                  (point-on-s2-not-d))
                                     p)))
                 (:instance b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6-1
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (a-1 (b-inv-rotation (acl2-sqrt 2)))
                            (r (rotation-3d
                                (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                (point-on-s2-not-d)))
                            (wit-wit (set-r-1-b-inv-r-a12-1-witness (b3-0-set-r-1-b-inv-r-a12-1-witness p)))
                            (wit (b3-0-set-r-1-b-inv-r-a12-1-witness p))
                            (id-1 (id-rotation))
                            (a-1-1 (b-inv-rotation (acl2-sqrt 2)))
                            (a (b-rotation (acl2-sqrt 2)))
                            (id-2 (id-rotation))
                            (r1 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (id-3 (id-rotation))
                            (wit-wit-1 (set-r-1-b-inv-r-a12-1-witness (b3-0-set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance m-*point-id=point
                            (p1 (set-r-1-b-inv-r-a12-1-witness (b3-0-set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance set-a12 (p (set-r-1-b-inv-r-a12-1-witness (b3-0-set-r-1-b-inv-r-a12-1-witness p))))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-3
                            (wit-wit (set-r-1-b-inv-r-a12-1-witness (b3-0-set-r-1-b-inv-r-a12-1-witness p)))
                            (r-1-rot (m-*
                                      (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                       0 (* 2 (acl2-pi))))
                                                   (point-on-s2-not-d))
                                      (b-rotation (acl2-sqrt 2))
                                      (rotation-3d
                                       (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                       (point-on-s2-not-d))))
                            (a (/ (cal-radius p)))
                            (p p))
                 (:instance m1=m2/a=>m1=s-*/a-m2
                            (p1 (b3-0-set-r-1-b-inv-r-a12-1-witness p))
                            (p2 p)
                            (a (/ (cal-radius p))))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-x1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-y1 p)))
                 (:instance b3-0-a-1-a3-iff-a-1-b3-0-a3-2
                            (x (/ (cal-radius p)))
                            (y (point-in-r3-z1 p)))
                 (:instance b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6-2
                            (wit-wit (set-r-1-b-inv-r-a12-1-witness (b3-0-set-r-1-b-inv-r-a12-1-witness p)))
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (b-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (wit (b3-0-set-r-1-b-inv-r-a12-1-witness p))
                            (s (s-* (/ (cal-radius p)) p)))
                 (:instance b3-0-r-1-a-inv-r-b3-0-a6-iff-b3-0-r-1-a-1-r-a6-2
                            (m1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                 0 (* 2 (acl2-pi))))
                                             (point-on-s2-not-d)))
                            (m2 (b-rotation (acl2-sqrt 2)))
                            (m3 (rotation-3d
                                 (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                 (point-on-s2-not-d)))
                            (m4 (s-* (/ (cal-radius p)) p)))
                 (:instance r3-matrixp
                            (m (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance pr3-p=>pr3-a*p
                            (a (/ (cal-radius p)))
                            (p (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d))
                                    p)))
                 (:instance pr3=>r^2>=0 (p p))
                 (:instance normalize-dimensions-name (name '$arg) (l p))
                 (:instance normalize-dimensions-name (name '$arg)
                            (l (m-* (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                     0 (* 2 (acl2-pi))))
                                                 (point-on-s2-not-d))
                                    (b-rotation (acl2-sqrt 2))
                                    (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi)))
                                                 (point-on-s2-not-d)))))
                 (:instance point-in-r3 (x p))
                 (:instance array2p-alist2p
                            (name :fake-name)
                            (l p))
                 (:instance id*m=m (m1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi))) (point-on-s2-not-d))))
                 (:instance r3-rotationp (m (rotation-3d
                                             (exists-in-interval-but-not-in-angle-sequence-witness 0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d))))
                 (:instance funs-lemmas-1 (x (acl2-sqrt 2)))
                 (:instance funs-lemmas-2 (x (acl2-sqrt 2)))
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-6)
                 (:instance b3-0-a-1-r-a4=>b3-0-a-1-r-b3-0-a4-4)
                 (:instance b3-0-r-1-a-1-r-a6=>b3-0-r-1-a-inv-r-b3-0-a6-3
                            (r (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                             0 (* 2 (acl2-pi)))
                                            (point-on-s2-not-d)))
                            (r1 (rotation-3d (exists-in-interval-but-not-in-angle-sequence-witness
                                              0 (* 2 (acl2-pi)))
                                             (point-on-s2-not-d)))
                            (r-1 (rotation-3d (- (exists-in-interval-but-not-in-angle-sequence-witness
                                                  0 (* 2 (acl2-pi))))
                                              (point-on-s2-not-d)))
                            (id-1 (id-rotation))
                            (id-2 (id-rotation))
                            (id-3 (id-rotation))
                            (p p)
                            (a-1 (b-inv-rotation (acl2-sqrt 2)))
                            (a (b-rotation (acl2-sqrt 2)))
                            (a1 (b-rotation (acl2-sqrt 2))))
                 (:instance m-*point-id=point (p1 p))
                 )
           :in-theory nil
           )))

(defthmd b3-0-r-1-b-inv-r-b3-0-a12-iff-b3-0-r-1-b-1-r-a12
  (iff (b3-0-r-1-b-inv-r-b3-0-set-a12 p)
       (b3-0-set-r-1-b-inv-r-a12 p))
  :hints (("Goal"
           :use ((:instance b3-0-r-1-b-inv-r-b3-0-a12=>b3-0-r-1-b-1-r-a12)
                 (:instance b3-0-r-1-b-1-r-a12=>b3-0-r-1-b-inv-r-b3-0-a12))
           :in-theory (disable (:executable-counterpart tau-system))
           )))

(defthmd b3-0=>a9-to-a14
  (implies (b3-0-s2 p)
           (or (b3-0-set-b-inv-a9 p)
               (b3-0-set-b-inv-r-a10 p)
               (b3-0-set-r-1-b-inv-a11 p)
               (b3-0-set-r-1-b-inv-r-a12 p)
               (b3-0-set-a13 p)
               (b3-0-set-a14 p)))
  :hints (("goal"
           :use ((:instance b3-0-s2 (p p))
                 (:instance b3-0-s2-1 (p p))
                 (:instance s2-equiv-3 (p (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-b-inv-a9 (p p))
                 (:instance b3-0-set-b-inv-a9-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-b-inv-r-a10 (p p))
                 (:instance b3-0-set-b-inv-r-a10-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-r-1-b-inv-a11 (p p))
                 (:instance b3-0-set-r-1-b-inv-a11-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-r-1-b-inv-r-a12 (p p))
                 (:instance b3-0-set-r-1-b-inv-r-a12-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a13 (p p))
                 (:instance b3-0-set-a13-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 (:instance b3-0-set-a14 (p p))
                 (:instance b3-0-set-a14-1-suff (p p) (p-s2 (b3-0-s2-1-witness p)))
                 )
           :in-theory nil
           )))

(defthmd a9-to-a14=>b3-0
  (implies (or (b3-0-set-b-inv-a9 p)
               (b3-0-set-b-inv-r-a10 p)
               (b3-0-set-r-1-b-inv-a11 p)
               (b3-0-set-r-1-b-inv-r-a12 p)
               (b3-0-set-a13 p)
               (b3-0-set-a14 p))
           (b3-0 p))
  :hints (("goal"
           :in-theory (disable b3-0-set-b-inv-a9-1
                               b3-0-set-b-inv-r-a10-1
                               b3-0-set-r-1-b-inv-a11-1
                               b3-0-set-r-1-b-inv-r-a12-1
                               b3-0-set-a13-1
                               b3-0-set-a14-1)
           )))

(defthmd b3-0-iff-a9-to-a14-1
  (iff (or (b3-0-s2 p)
           (b3-0 p))
       ;; (or (or (b3-0-set-b-inv-a9 p)
       ;;         (b3-0-set-b-inv-r-a10 p)
       ;;         (b3-0-set-r-1-b-inv-a11 p)
       ;;         (b3-0-set-r-1-b-inv-r-a12 p)
       ;;         (b3-0-set-a13 p)
       ;;         (b3-0-set-a14 p))
       (or (b3-0-b-inv-b3-0-set-a9 p)
           (b3-0-b-inv-r-b3-0-set-a10 p)
           (b3-0-r-1-b-inv-b3-0-set-a11 p)
           (b3-0-r-1-b-inv-r-b3-0-set-a12 p)
           (b3-0-set-a13 p)
           (b3-0-set-a14 p)))
  :hints (("goal"
           :use ((:instance b3-0-iff-b3-0-s2 (p p))
                 (:instance b3-0=>a9-to-a14 (p p))
                 (:instance a9-to-a14=>b3-0 (p p))
                 (:instance b3-0-r-1-b-inv-r-b3-0-a12-iff-b3-0-r-1-b-1-r-a12)
                 (:instance b3-0-r-1-b-inv-b3-0-a11-iff-b3-0-r-1-b-1-a11)
                 (:instance b3-0-b-1-r-b3-0-a10-iff-b3-0-b-1-r-a10)
                 (:instance b3-0-b-1-b3-0-a9-iff-b3-0-b-1-a9))
           :in-theory nil
           )))

(defthmd b3-0-iff-a1-to-a14
  (iff (b3-0 p)
       (or (b3-0-set-a1 p)
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
           (b3-0-set-a14 p)))
  :hints (("goal"
           :use ((:instance b3-0-iff-b3-0-s2 (p p))
                 (:instance b3-0-iff-a1-to-a14-1 (p p)))
           :in-theory nil
           )))

(defthmd b3-0-iff-a3-to-a8
  (iff (b3-0 p)
       (or (b3-0-a-inv-b3-0-set-a3 p)
           (b3-0-a-inv-r-b3-0-set-a4 p)
           (b3-0-r-1-a-inv-b3-0-set-a5 p)
           (b3-0-r-1-a-inv-r-b3-0-set-a6 p)
           (b3-0-set-a7 p)
           (b3-0-set-a8 p)))
  :hints (("goal"
           :use ((:instance b3-0-iff-b3-0-s2 (p p))
                 (:instance b3-0-iff-a3-to-a8-1 (p p)))
           :in-theory nil
           )))

(defthmd b3-0-iff-a9-to-a14
  (iff (b3-0 p)
       (or (b3-0-b-inv-b3-0-set-a9 p)
           (b3-0-b-inv-r-b3-0-set-a10 p)
           (b3-0-r-1-b-inv-b3-0-set-a11 p)
           (b3-0-r-1-b-inv-r-b3-0-set-a12 p)
           (b3-0-set-a13 p)
           (b3-0-set-a14 p)))
  :hints (("goal"
           :use ((:instance b3-0-iff-b3-0-s2 (p p))
                 (:instance b3-0-iff-a9-to-a14-1 (p p)))
           :in-theory nil
           )))
