(in-package "ACL2")

(local
(encapsulate
    ()

(encapsulate
    (
     ((local-ifloor * *) => *)
     ((local-imod * *) => *)
     ((local-expt2 *) => *)
     ((local-logcar *) => *)
     ((local-loghead * *) => *)
     ((local-logapp * * *) => *)
     )

  (local
   (encapsulate
       ()

     (defun local-ifloor (i j)
       (floor (ifix i) (ifix j)))
     
     (defun local-imod (i j)
       (mod (ifix i) (ifix j)))
     
     (defun local-expt2 (n)
       (expt 2 (nfix n)))
     
     (defun local-logcar (i)
       (local-imod i 2))
     
     (defun local-loghead (size i)
       (local-imod i (local-expt2 size)))
     
     (defun local-logapp (size i j) 
       (let ((j (ifix j)))
	 (+ (local-loghead size i) (* j (local-expt2 size)))))

     ))

  (defthm local-ifloor-defn
    (equal (local-ifloor i j)
	   (floor (ifix i) (ifix j))))
  
  (defthm local-imod-defn 
    (equal (local-imod i j)
	   (mod (ifix i) (ifix j))))
  
  (defthm local-expt2-defn 
    (equal (local-expt2 n)
	   (expt 2 (nfix n))))
  
  (defthm local-logcar-defn
    (equal (local-logcar i)
	   (local-imod i 2)))
  
  (defthm local-loghead-defn
    (equal (local-loghead size i)
	   (local-imod i (local-expt2 size))))
  
  (defthm local-logapp-defn
    (equal (local-logapp size i j) 
	   (let ((j (ifix j)))
	     (+ (local-loghead size i) (* j (local-expt2 size))))))
  
  )


(encapsulate
    ()

  (local
   (encapsulate
       ()
     
     (include-book "arithmetic-3/bind-free/top" :dir :system)
     
     (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)
     
     (SET-DEFAULT-HINTS '((NONLINEARP-DEFAULT-HINT STABLE-UNDER-SIMPLIFICATIONP
						   HIST PSPV)))
     
     (defthm crock
       (implies (integerp x)
		(integerp (* x (/ x)))))
     
     (defthm mod-+-1
       (implies (and (integerp x)
		     (integerp n)
		     (< 1 n))
		(equal (mod (+ 1 x) n)
		       (if (integerp (/ (+ 1 x) n))
			   0
			 (+ 1 (mod x n)))))
       :hints (("Goal" :in-theory (enable mod))
	       ("Subgoal 1'6'" :use (:instance crock
					       (x (+ i 1)))
		:in-theory (disable |(* a (/ a))|)))
       :otf-flg t)
     
     (defthm integerp-crock
       (implies (and (< 0 x)
		     (< x 1))
		(not (integerp x))))
     
     (defthm not-integerp-/-expt-2-n
       (implies (and (integerp n)
		     (< 0 n))
		(not (integerp (/ (expt 2 n))))))
     
     (defthm integerp-crock-2a
       (implies (integerp x)
		(integerp (* 2 x))))
     
     (defthm integerp-crock-2
       (implies (and (rationalp x)
		     (not (integerp x)))
		(not (integerp (* 1/2 x))))
       :hints (("Goal" :use (:instance integerp-crock-2a
				       (x (* 1/2 x))))))
     
     (defun ind-fn (n)
       (if (zp n)
	   0
	 (ind-fn (+ -1 n))))
     
     (defthm integerp-crock-3
       (implies (and (integerp v)
		     (integerp n)
		     (< 0 n)
		     (integerp (* 1/2 v)))
		(not (integerp (+ (/ (expt 2 n))
				  (* v (/ (expt 2 n)))))))
       :hints (("Goal" :induct (ind-fn n))
	       ("Subgoal *1/2.1" :use (:instance integerp-crock-2
						 (x (+ (/ (EXPT 2 (+ -1 N)))
						       (* V (/ (EXPT 2 (+ -1 
									  N))))))))))
     
     ))
  
  (defthm plus-of-local-logapp-suck-in-local-logcar
    (implies
     (and
      (natp n)
      (< 0 n)
      (integerp v)
      (integerp x)
      (equal (local-logcar v) 0))
     (equal (+ 1 (local-logapp n v x))
	    (local-logapp n (+ 1 v) x)))
    :hints (("Goal" :cases ((equal n 1))))
    :otf-flg t)
  
  )

))

(include-book "ihs/ihs-lemmas" :dir :system)

(defthm plus-of-logapp-suck-in-logcar
    (implies
     (and
      (natp n)
      (< 0 n)
      (integerp v)
      (integerp x)
      (equal (logcar v) 0))
     (equal (+ 1 (logapp n v x))
	    (logapp n (+ 1 v) x)))
    :hints (("Goal" :in-theory `(logapp loghead logcar expt2 imod ifloor)
	     :use (:functional-instance
		   plus-of-local-logapp-suck-in-local-logcar
		   (local-ifloor ifloor)
		   (local-imod   imod)
		   (local-expt2  expt2)
		   (local-logcar logcar)
		   (local-loghead loghead)
		   (local-logapp  logapp)))))
