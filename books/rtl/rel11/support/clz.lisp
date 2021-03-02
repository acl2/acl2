(in-package "RTL")

(include-book "basic")
(include-book "bits")
(include-book "log")
(include-book "float")
(include-book "definitions")
(add-macro-alias cat binary-cat)
(include-book "arithmetic-5/top" :dir :system)

(defund zseg (x k i)
  (if (zp k)
      (if (= (bitn x i) 0)
	  1
	0)
    (if (and (= (zseg x (1- k) (1+ (* 2 i))) 1)
	     (= (zseg x (1- k) (* 2 i)) 1))
	1
      0)))

(defund zcount (x k i)
  (if (zp k)
      0
    (if (= (zseg x (1- k) (1+ (* 2 i))) 1)
	(logior (expt 2 (1- k)) (zcount x (1- k) (* 2 i)))
      (zcount x (1- k) (1+ (* 2 i))))))

(defund clz (x n)
  (zcount x n 0))

(defund seg (x k i)
  (bits x (1- (* (expt 2 k) (1+ i))) (* (expt 2 k) i)))

(defthmd seg-cat
  (implies (and (integerp x)
		(not (zp k))
		(natp i))
	   (equal (seg x k i)
		  (cat (seg x (1- k) (1+ (* 2 i))) (expt 2 (1- k))
		       (seg x (1- k) (* 2 i)) (expt 2 (1- k)))))
  :hints (("Goal" :nonlinearp t :in-theory (enable seg cat-0))))
  
(defthm bvecp-seg
  (implies (and (natp k) (natp i))
	   (bvecp (seg x k i) (expt 2 k)))
  :hints (("Goal" :in-theory (enable seg bvecp)
	          :use ((:instance bits-bounds (i (1- (* (expt 2 k) (1+ i)))) (j (* (expt 2 k) i)))))))

(defthmd z-val
  (implies (and (integerp x)
		(natp k)
		(natp i))
	   (equal (zseg x k i)
		  (if (= (seg x k i) 0)
		      1 0)))
  :hints (("Goal" :nonlinearp t :in-theory (enable seg-cat cat zseg))
	  ("Subgoal *1/2" :in-theory (enable zseg seg))
	  ("Subgoal *1/1" :in-theory (enable zseg seg))))

(defthmd expo-seg
  (implies (and (integerp x)
		(natp k)
		(natp i))
	   (and (>= (expo (seg x k i)) 0)
		(<= (expo (seg x k i)) (1- (expt 2 k)))))
  :hints (("Goal" :in-theory (enable seg)
	          :use ((:instance bits-bounds (i (1- (* (expt 2 k) (1+ i)))) (j (* (expt 2 k) i)))
		        (:instance expo<= (x (seg x k i)) (n (1- (expt 2 k))))
		        (:instance expo>= (x (seg x k i)) (n 0))))))

(defthmd c-val-1
  (implies (and (integerp x)
		(not (zp k))
		(natp i)
		(equal (zseg x k i) 0)
		(not (equal (zseg x (1- k) (1+ (* 2 i))) 0))
		(equal (zcount x (1- k) (* 2 i))
		       (1- (- (expt 2 (1- k)) (expo (seg x (1- k) (* 2 i)))))))		     
	   (equal (zcount x k i)
		  (1- (- (expt 2 k) (expo (seg x k i))))))
  :hints (("Goal" :nonlinearp t
                  :use ((:instance expo-seg (k (1- k)) (i (* 2 i)))
		        (:instance logior-expt-cor (n (1- k)) (x 1) (y (zcount x (1- k) (* 2 i)))))
	          :in-theory (enable bvecp zcount seg-cat cat-0 z-val))))

(defthmd c-val-2
  (implies (and (integerp x)
		(not (zp k))
		(natp i))
	   (>= (seg x k i)
	       (* (expt 2 (expt 2 (1- k)))
	          (seg x (1- k) (1+ (* 2 i))))))
  :hints (("Goal" :nonlinearp t
	          :in-theory (enable bvecp seg-cat cat)
		  :use ((:instance bvecp-seg (k (1- k)) (i (* 2 i)))))))

(defthmd c-val-3
  (implies (and (integerp x)
		(not (zp k))
		(natp i)
		(equal (zseg x (1- k) (1+ (* 2 i))) 0))
	   (>= (* (expt 2 (expt 2 (1- k)))
	          (seg x (1- k) (1+ (* 2 i))))
	       (expt 2 (+ (expt 2 (1- k))
	                  (expo (seg x (1- k) (1+ (* 2 i))))))))
  :hints (("Goal" :nonlinearp t
	          :in-theory (enable seg-cat cat z-val)
		  :use (c-val-2
		        (:instance expo-lower-bound (x (seg x (1- k) (1+ (* 2 i)))))))))

(defthmd c-val-4
  (implies (and (integerp x)
		(not (zp k))
		(natp i)
		(equal (zseg x (1- k) (1+ (* 2 i))) 0))
	   (>= (seg x k i)
	       (expt 2 (+ (expt 2 (1- k))
	                  (expo (seg x (1- k) (1+ (* 2 i))))))))
  :hints (("Goal" :use (c-val-2 c-val-3) :in-theory (theory 'minimal-theory))))

(defthmd c-val-5
  (implies (and (integerp x)
		(not (zp k))
		(natp i)
		(equal (zseg x (1- k) (1+ (* 2 i))) 0))
	   (>= (expo (seg x k i))
	       (+ (expt 2 (1- k))
	          (expo (seg x (1- k) (1+ (* 2 i)))))))
  :hints (("Goal" :use (c-val-4
                        (:instance expo>= (x (seg x k i)) (n (+ (expt 2 (1- k)) (expo (seg x (1- k) (1+ (* 2 i)))))))))))

(defthmd c-val-6
  (implies (and (integerp x)
		(not (zp k))
		(natp i))
	   (< (seg x k i)
	      (* (expt 2 (expt 2 (1- k)))
	         (1+ (seg x (1- k) (1+ (* 2 i)))))))
  :hints (("Goal" :nonlinearp t
	          :in-theory (enable seg-cat cat))
          ("Goal''" :in-theory (e/d (bvecp) (bvecp-seg))
		    :use ((:instance bvecp-seg (k (1- k)) (i (* 2 i)))))))

(defthmd c-val-7
  (implies (and (integerp x)
		(not (zp k))
		(natp i)
		(equal (zseg x (1- k) (1+ (* 2 i))) 0))
	   (<= (* (expt 2 (expt 2 (1- k)))
	          (1+ (seg x (1- k) (1+ (* 2 i)))))
	       (expt 2 (+ (expt 2 (1- k)) (expo (seg x (1- k) (1+ (* 2 i)))) 1))))
  :hints (("Goal" :nonlinearp t
	          :use ((:instance expo-upper-bound (x (seg x (1- k) (1+ (* 2 i)))))
		        (:instance expo>= (x (seg x (1- k) (1+ (* 2 i)))) (n 0))))))

(defthmd c-val-8
  (implies (and (integerp x)
		(not (zp k))
		(natp i)
		(equal (zseg x (1- k) (1+ (* 2 i))) 0))
	   (< (seg x k i)
	      (expt 2 (+ (expt 2 (1- k)) (expo (seg x (1- k) (1+ (* 2 i)))) 1))))
  :hints (("Goal" :use (c-val-6 c-val-7)
                  :in-theory (theory 'minimal-theory))))

(defthmd c-val-9
  (implies (and (integerp x)
		(not (zp k))
		(natp i)
		(equal (zseg x (1- k) (1+ (* 2 i))) 0))
	   (< (expo (seg x k i))
	      (+ (expt 2 (1- k)) (expo (seg x (1- k) (1+ (* 2 i)))) 1)))
  :hints (("Goal" :use (c-val-4 c-val-8 (:instance expo<= (x (seg x k i)) (n (+ (expt 2 (1- k)) (expo (seg x (1- k) (1+ (* 2 i)))))))))))

(defthmd c-val-10
  (implies (and (integerp x)
		(not (zp k))
		(natp i)
		(equal (zseg x (1- k) (1+ (* 2 i))) 0))
	   (equal (expo (seg x k i))
	          (+ (expt 2 (1- k))
	             (expo (seg x (1- k) (1+ (* 2 i)))))))
  :hints (("Goal" :use (c-val-5 c-val-9))))

(defthmd c-val-11
  (implies (and (integerp x)
		(not (zp k))
		(natp i)
		(equal (zseg x (1- k) (1+ (* 2 i))) 0)
		(equal (zcount x (1- k) (1+ (* 2 i)))
		       (1- (- (expt 2 (1- k)) (expo (seg x (1- k) (1+ (* 2 i))))))))
	   (equal (zcount x k i)
	          (1- (- (expt 2 k) (expo (seg x k i))))))
  :hints (("Goal" :use (c-val-10)
                  :in-theory (enable zcount))))

(defun c-induct (x k i)
  (if (zp k)
      0
    (if (= (zseg x (1- k) (1+ (* 2 i))) 1)
        (1+ (c-induct x (1- k) (* 2 i)))
      (c-induct x (1- k) (1+ (* 2 i))))))

(defthmd c-val
  (implies (and (integerp x)
		(natp k)
		(natp i)
		(equal (zseg x k i) 0))
	   (equal (zcount x k i)
	          (1- (- (expt 2 k) (expo (seg x k i))))))
  :hints (("Goal" :induct (c-induct x k i))
          ("Subgoal *1/3" :use (c-val-11))
          ("Subgoal *1/2" :in-theory (enable zseg) :use (c-val-1))
          ("Subgoal *1/1" :in-theory (enable zseg zcount seg))))

(defthmd clz-thm
  (implies (and (natp n)
                (bvecp x (expt 2 n))
		(> x 0))
	   (equal (clz x n)
	          (- (1- (expt 2 n)) (expo x))))
  :hints (("Goal" :in-theory (enable clz z-val c-val seg))))

