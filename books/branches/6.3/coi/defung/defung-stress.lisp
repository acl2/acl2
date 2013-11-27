#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "defung")

#+joe
(defmacro hide-local (&rest args)
  `(encapsulate
       ()
     (local
      (encapsulate
	  ()
	,@args))))

(defmacro hide-local (&rest args)
  `(local
    (encapsulate
	()
      ,@args)))

(local
 (defstub zed-test (x) nil))

(hide-local
 (def::ung zzedc (a b c) 
   (let ((val (if (zed-test a) b (zzedc (1+ a) b c))))
     (if (zed-test c) val
       (zzedc val 
	      (if (zed-test val) c (zzedc (1+ a) (1+ b) (1+ c))) 
	      (if (zed-test b) 
		  (if (zed-test val) c 
		    (zzedc (1+ a) (1+ b) (1+ c))) 
		(zzedc (1+ a) (1- b) c)))))))

(hide-local
 (def::ung zzedb (a b c) 
   (if (zed-test c) (if (zed-test a) b (zzedb (1+ a) b c))
     (zzedb (if (zed-test a) b (zzedb (1+ a) b c)) 
	    (if (zed-test (if (zed-test a) b (zzedb (1+ a) b c))) 
		c 
	      (zzedb (1+ a) (1+ b) (1+ c))) 
	    (if (zed-test b) 
		(if (zed-test (if (zed-test a) b (zzedb (1+ a) b c))) c 
		  (zzedb (1+ a) (1+ b) (1+ c))) 
	      (zzedb (1+ a) (1- b) c))))))

(hide-local
 (def::ung zed1 (x)
   (if (< x 0) (+ x 3)
     (let ((x (zed1 (1- x))))
       (if (< x 0) (zed1 (- x 2))
	 (zed1 (- x 3)))))))

(hide-local
 (def::ung zed2 (x)
   (if (< x 0) (+ x 3)
     (let ((x (zed2 (- x 1))))
       (if (< x 0) (zed2 (- x 2))
	 (let ((x (zed2 (- x 3))))
	   (if (< x 0) (zed2 (- x 4))
	     (zed2 (- x 5)))))))))

;; ==================================================================
;;
;; A bunch of other stress tests ..
;;
;; ==================================================================

(hide-local
 
 (def::ung zedA (a b c) (if (zed-test a) (zedA (1+ a) b c) (+ b c)))
 
 (defthm zedA_check
   (implies
    (zedA-domain a b c)
    (equal (zedA a b c)
	   (if (zed-test a) (zedA (1+ a) b c) (+ b c)))))
 
 )


(hide-local
 
 (def::ung zed22 (a b c) 
   (if (zed-test a) (+ b c)
     (+ (zed22 (1+ a) (zed22 (+ 2 a) b c)
	      (+ (zed22 (+ 3 a) (+ b c) c)
		 (zed22 b (+ a c) a))))))
 
 (defthm zed22_check
   (implies
    (zed22-domain a b c)
    (equal (zed22 a b c)
	   (if (zed-test a) (+ b c)
	     (+ (zed22 (1+ a) (zed22 (+ 2 a) b c)
		      (+ (zed22 (+ 3 a) (+ b c) c)
			 (zed22 b (+ a c) a))))))))
 
 )

(hide-local
 
 (def::ung yak (m n)
   (cond
    ((equal m 0) (+ n 1))
    ((and (< 0 m) (= n 0)) (yak (1- m) 1))
    (t (yak (1- m) (yak m (1- n))))))
 
 (defthm yak_check
   (implies
    (yak-domain m n)
    (equal (yak m n)
	   (cond
	    ((equal m 0) (+ n 1))
	    ((and (< 0 m) (= n 0)) (yak (1- m) 1))
	    (t (yak (1- m) (yak m (1- n)))))))
   :hints (("Goal" :in-theory (disable (yak) (yak-domain)))))

 )


(hide-local
 
 (def::ung zed3 (a b c) 
   (let ((z (+ a b c)))
     (if (zed-test z) (+ a b c)
       (zed3 (1- a) (1- b) (1- c)))))
 
 (defthm zed3_check
   (implies
    (zed3-domain a b c)
    (equal (zed3 a b c)
	   (let ((z (+ a b c)))
	     (if (zed-test z) (+ a b c)
	       (zed3 (1- a) (1- b) (1- c)))))))
 )

;; here it detects that the recursive call is governed by zed-test
;; and it produces a resonable induction scheme to go along with
;; it.
(hide-local
 
 (def::ung zed4 (a b c) 
   (cons (if (zed-test a) (zed4 (1- a) b c) (+ a b c))
	 (list a b c)))
 
 (defthm zed4_check
   (implies
    (zed4-domain a b c)
    (equal (zed4 a b c) 
	   (cons (if (zed-test a) (zed4 (1- a) b c) (+ a b c))
		 (list a b c)))))
 
 )

(hide-local
 
 (def::ung zzed (a b c) 
   (if (zed-test c) (if (zed-test a) b (zzed (1+ a) b c))
     (zzed (if (zed-test a) b (zzed (1+ a) b c)) 
	   (if (zed-test (if (zed-test a) b (zzed (1+ a) b c))) 
	       c 
	     (zzed (1+ a) (1+ b) (1+ c))) 
	   (if (zed-test b) 
	       (if (zed-test (if (zed-test a) b (zzed (1+ a) b c))) c 
		 (zzed (1+ a) (1+ b) (1+ c))) 
	     (zzed (1+ a) (1- b) c)))))
 
 (defthm zzed-check-1
   (implies
    (zzed-domain a b c)
    (equal (zzed a b c)
	   (if (zed-test c) (if (zed-test a) b (zzed (1+ a) b c))
	     (zzed (if (zed-test a) b (zzed (1+ a) b c)) 
		   (if (zed-test (if (zed-test a) b (zzed (1+ a) b c))) 
		       c 
		     (zzed (1+ a) (1+ b) (1+ c))) 
		   (if (zed-test b) 
		       (if (zed-test (if (zed-test a) b (zzed (1+ a) b c))) c 
			 (zzed (1+ a) (1+ b) (1+ c))) 
		     (zzed (1+ a) (1- b) c)))))))
 
 ;;
 ;; Note that zzed is (should be) provably equivalent to zed5 (below) ..
 ;;
 (defthm zzed-check-2
   (implies
    (zzed-domain a b c)
    (equal (zzed a b c)
	   (let ((x (if (zed-test a) b (zzed (1+ a) b c))))
	     (let ((y (if (zed-test x) c (zzed (1+ a) (1+ b) (1+ c)))))
	       (let ((z (if (zed-test b) y (zzed (1+ a) (1- b) c))))
		 (if (zed-test c) x
		   (zzed x y z))))))))

 )

(hide-local
 
 (def::ung zed5 (a b c) 
   (let ((x (if (zed-test a) b (zed5 (1+ a) b c))))
     (let ((y (if (zed-test x) c (zed5 (1+ a) (1+ b) (1+ c)))))
       (let ((z (if (zed-test b) y (zed5 (1+ a) (1- b) c))))
	 (if (zed-test c) x
	   (zed5 x y z))))))
 
 ;;
 ;; Hmm .. this proof
 ;; a) doesn't work without zed5-definition
 ;; b) is really slow.
 ;;
 (defthm zed5-check
   (implies
    (zed5-domain a b c)
    (equal (zed5 a b c)
	   (let ((x (if (zed-test a) b (zed5 (1+ a) b c))))
	     (let ((y (if (zed-test x) c (zed5 (1+ a) (1+ b) (1+ c)))))
	       (let ((z (if (zed-test b) y (zed5 (1+ a) (1- b) c))))
		 (if (zed-test c) x
		   (zed5 x y z)))))))
   :hints (("Goal" :restrict ((zed5-definition ((a a) (b b) (c c))))
	    :in-theory (enable ZED5-DEFINITION))))
 
 )

(hide-local
 (def::ung one-4 (n)
   (if (zp n) 1
     (let ((n (if (< n 7) (1+ n) (1- n))))
       (let ((n (one-4 n)))
	 (let ((n (if (> n 10) (1- n) (1+ n))))
	   (let ((n (if (< (if (< (one-4 n) n) (one-4 (1+ n)) (1+ (one-4 n))) n) (one-4 (1+ n)) (one-4 (1- n)))))
	     (one-4 n)))))))
 )
