(in-package "RTL")

(include-book "norm")

(local-defthmd drnd-modep-mode
  (implies (not (specialp))
           (equal (drnd (* (a) (b)) (mode) (dp))
	          (if (< (* (a) (b)) 0)
		      (- (drnd (abs (* (a) (b))) (modep) (dp)))
		    (drnd (abs (* (a) (b))) (modep) (dp)))))
  :hints (("Goal" :in-theory (enable modep mode flip-mode rmode common-mode-p)
                  :use ((:instance drnd-minus (mode (modep)) (x (* (a) (b))) (f (dp)))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defund x0 ()
  (+ (expt 2 53) (bits (frac105) 104 52)))

(local-defund z0 ()
  (* (expt 2 (+ 52 (1- (expt 2 10))))
     (+ (abs (* (a) (b)))
        (expt 2 (- 2 (expt 2 10))))))

(local-in-theory (disable (x0) (z0)))

(local-in-theory (disable abs))

(local-defthmd denorm-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (and (<= (bits (frac105) 104 52)
                    (* (expt 2 (+ 52 (1- (expt 2 10))))
                       (abs (* (a) (b)))))
                (< (* (expt 2 (+ 52 (1- (expt 2 10))))
                      (abs (* (a) (b))))
	           (1+ (bits (frac105) 104 52)))))
  :hints (("Goal" :use (unround-b)
                  :nonlinearp t)))

(local-defthmd denorm-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (fl (z0)) (x0)))
  :hints (("Goal" :in-theory (enable x0 z0)
           :use (denorm-1))))

(local-defthmd denorm-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (stk)
	          (if (integerp (z0))
		      0 1)))	        
  :hints (("Goal" :in-theory (enable stk-rewrite x0 z0)
                  :use (unround-b denorm-1))))

(local-defthmd denorm-4
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (expo (x0)) 53))
  :hints (("Goal" :use ((:instance expo-unique (x (x0)) (n 53))
                        (:instance bits-bounds (x (frac105)) (i 104) (j 52)))
	          :in-theory (enable abs x0)
		  :nonlinearp t)))

(local-defthmd denorm-5
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (sgn (x0)) 1))
  :hints (("Goal" :in-theory (enable sgn x0)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j
                                                                      52))))))

(local-in-theory (enable abs))

(local-defthmd denorm-6
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (rtz (x0) 53)
	          (* 2 (fl (/ (x0) 2)))))
  :hints (("Goal" :in-theory (enable rtz-rewrite denorm-4 denorm-5))))

(local-defthmd denorm-7
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (rtz (x0) 53)
	          (* 2 (+ (expt 2 52) (fracunrnd)))))
  :hints (("Goal" :in-theory (enable fracunrnd x0)
                  :use (denorm-6
		        (:instance bits-plus-bitn (x (frac105)) (n 104) (m 52))
		        (:instance bitn-0-1 (x (frac105)) (n 52))))))

(local-defthmd denorm-8
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (fp+ (rtz (x0) 53) 53)
	          (+ (rtz (x0) 53) 2)))
  :hints (("Goal" :in-theory (enable fp+ denorm-4))))

(local-defthmd denorm-9
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (fp+ (rtz (x0) 53) 53)
	          (* 2 (+ (expt 2 52) (fracp1)))))
  :hints (("Goal" :in-theory (enable bvecp fracunrnd fracp1 denorm-7)
                  :use (denorm-8 (:instance bits-bounds (x (frac105)) (i 104) (j 53))))))

(local-defthmd denorm-10
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (bits (x0) 52 0)
	          (bits (frac105) 104 52)))
  :hints (("Goal" :in-theory (enable x0 bits-mod)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 52))))))

(local-defthmd denorm-11
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (bitn (x0) 0)
	          (grd)))
  :hints (("Goal" :in-theory (enable grd-rewrite denorm-10)
                  :use (denorm-8
		        (:instance bitn-bits (x (frac105)) (i 104) (j 52) (k 0))
		        (:instance bitn-bits (x (x0)) (i 52) (j 0) (k 0))))))

(local-defthmd denorm-12
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (bitn (x0) 1)
	          (lsb)))
  :hints (("Goal" :in-theory (enable lsb-rewrite denorm-10)
                  :use (denorm-8
		        (:instance bitn-bits (x (frac105)) (i 104) (j 52) (k 1))
		        (:instance bitn-bits (x (x0)) (i 52) (j 0) (k 1))))))

(local-defthmd denorm-13
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (rndup)
	          (if (roundup-pos (x0) 53 (stk) (modep) 53)
		      1 0)))
  :hints (("Goal" :in-theory (enable sign-rewrite mode modep rmode roundup-pos rndup denorm-11 denorm-12
                                     stk-rewrite grd-rewrite lsb-rewrite)
                  :use ((:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthm rationalp-z0
  (rationalp (z0))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable z0))))

(local-defthmd denorm-14
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (>= (z0) (expt 2 53)))
  :hints (("Goal" :in-theory (enable x0)
                  :use (denorm-2))))

(local-defthmd denorm-15
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 0))
	   (equal (rnd (z0) (modep) 53)
	          (rtz (x0) 53)))
  :hints (("Goal" :in-theory (enable denorm-2 denorm-3 denorm-4 denorm-11 denorm-12 denorm-13)
                  :use (denorm-14 (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n 53))))))

(local-defthmd denorm-16
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (iff (exactp (z0) 53)
	        (and (= (stk) 0) (= (grd) 0))))
  :hints (("Goal" :in-theory (enable denorm-2 denorm-3 denorm-4 denorm-11 denorm-12 denorm-13)
                  :use (denorm-14 (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n 53))))))

(local-defthmd denorm-17
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 0))
	   (and (equal (exprndinc) 0)
	        (equal (rnd (z0) (modep) 53)
		       (* 2 (+ (expt 2 52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable bvecp denorm-7 denorm-15 exprndinc fracunrnd fracrnd))))

(local-defthmd denorm-18
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1))
	   (equal (rnd (z0) (modep) 53)
	          (fp+ (rtz (x0) 53) 53)))
  :hints (("Goal" :in-theory (enable denorm-2 denorm-3 denorm-4 denorm-11 denorm-12 denorm-13)
                  :use (denorm-14 (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n 53))))))

(local-defthmd denorm-19
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1))
	   (equal (rnd (z0) (modep) 53)
	          (* 2 (+ (expt 2 52) (fracp1)))))
  :hints (("Goal" :in-theory (enable denorm-18)
                  :use (denorm-9))))

(local-defthmd denorm-20
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1)
		(< (fracp1) (expt 2 52)))
	   (and (equal (exprndinc) 0)
  	        (equal (rnd (z0) (modep) 53)
	               (* 2 (+ (expt 2 52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable denorm-19 fracp1 fracunrnd fracrnd exprndinc bvecp)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 53))))))

(local-defthmd denorm-21
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1)
		(= (fracp1) (expt 2 52)))
	   (and (equal (exprndinc) 1)
  	        (equal (rnd (z0) (modep) 53)
	               (* 4 (+ (expt 2 52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable denorm-19 fracp1 fracunrnd fracrnd exprndinc bvecp)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 53))))))

(local-defthmd denorm-22
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (rndup) 1))
           (<= (fracp1) (expt 2 52)))
  :hints (("Goal" :in-theory (enable denorm-19 fracp1 fracunrnd fracrnd exprndinc bvecp)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 53))))))

(local-defthmd denorm-23
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (rnd (z0) (modep) 53)
	          (* (expt 2 (1+ (exprndinc)))
		     (+ (expt 2 52) (fracrnd)))))
  :hints (("Goal" :use (denorm-17 denorm-20 denorm-21 denorm-22)
           :in-theory (enable rndup))))

(local-in-theory (disable abs))

(local-defthmd denorm-24
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (rnd (+ (abs (* (a) (b))) (expt 2 (- 2 (expt 2 10)))) (modep) 53)                          
                  (* (expt 2 (- -52 (1- (expt 2 10))))
                     (rnd (z0) (modep) 53))))
  :hints (("Goal" :use ((:instance rnd-shift (mode (modep))
                                             (x (+ (abs (* (a) (b))) (expt 2 (- 2 (expt 2 10)))))
					     (k (+ 52 (1- (expt 2 10))))
					     (n 53)))
                  :in-theory (enable z0))))

(local-defthmd denorm-25
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (rnd (+ (abs (* (a) (b))) (expt 2 (- 2 (expt 2 10)))) (modep) 53)                          
                  (* (expt 2 (- (exprndinc) (+ 51 (1- (expt 2 10)))))
                     (+ (expt 2 52) (fracrnd)))))
  :hints (("Goal" :use (denorm-24)
                  :in-theory (enable denorm-23))))

(local-defthm denorm-26
  (implies (not (specialp))
	   (equal (sgn (abs (* (a) (b))))
	          1))
  :hints (("Goal" :in-theory (enable sgn abs a-nonzero b-nonzero))))

(local-defthm denorm-27
  (implies (rationalp x)
           (equal (abs (abs x)) (abs x)))
  :hints (("Goal" :in-theory (enable abs))))
  
(local-defthmd denorm-28
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
           (equal (drnd (abs (* (a) (b))) (modep) (dp))
                  (- (* (expt 2 (- (exprndinc) (+ 51 (1- (expt 2 10)))))
                        (+ (expt 2 52) (fracrnd)))
		     (expt 2 (- 2 (expt 2 10))))))
  :hints (("Goal" :use (underflow-2 denorm-25)
                  :in-theory (enable drnd-rewrite dp prec))))

(local-defthmd denorm-29
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (exprndinc) 1))
           (equal (fracrnd) 0))
  :hints (("Goal" :use ((:instance bitn-plus-bits (x (fracp1)) (n 52) (m 0))
                        (:instance bits-bounds (x (frac105)) (i 104) (j 53)))
                  :in-theory (enable fracrnd exprndinc bvecp fracunrnd fracp1))))

(local-defthmd denorm-30
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (exprndinc) 1))
           (equal (drnd (abs (* (a) (b))) (modep) (dp))
                  (* (expt 2 (- 2 (expt 2 10)))
                     (1+ (* (expt 2 -52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable denorm-28 denorm-29))))

(local-defthmd denorm-31
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (exprndinc) 0))
           (equal (drnd (abs (* (a) (b))) (modep) (dp))
                  (* (expt 2 (- -50 (expt 2 10)))
                     (fracrnd))))
  :hints (("Goal" :in-theory (enable denorm-28))))

(defthmd denorm-drnd-rndup
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (exprndinc) 1))
           (equal (drnd (* (a) (b)) (mode) (dp))
	          (if (< (* (a) (b)) 0)
		      (- (* (expt 2 (- 2 (expt 2 10)))
                            (1+ (* (expt 2 -52) (fracrnd)))))
	            (* (expt 2 (- 2 (expt 2 10)))
                       (1+ (* (expt 2 -52) (fracrnd)))))))
  :hints (("Goal" :in-theory (enable drnd-modep-mode denorm-30))))

(defthmd denorm-drnd-no-rndup
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0)
                (= (exprndinc) 0))
           (equal (drnd (* (a) (b)) (mode) (dp))
	          (if (< (* (a) (b)) 0)
		      (- (* (expt 2 (- -50 (expt 2 10)))
                            (fracrnd)))
	            (* (expt 2 (- -50 (expt 2 10)))
                       (fracrnd)))))
  :hints (("Goal" :in-theory (enable drnd-modep-mode denorm-31))))

(local-defthmd denorm-32
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (iff (exactp (+ (abs (* (a) (b)))
                           (expt 2 (- 2 (expt 2 10))))
			53)
	        (and (= (stk) 0) (= (grd) 0))))
  :hints (("Goal" :in-theory (enable z0)
                  :use (denorm-16
		        (:instance exactp-shift (x (+ (abs (* (a) (b))) (expt 2 (- 2 (expt 2 10)))))
		                                (k (+ 52 (1- (expt 2 10))))
						(n 53))))))

(local-defthmd denorm-33
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (iff (= (rnd (+ (abs (* (a) (b)))
                           (expt 2 (- 2 (expt 2 10))))
			(modep)
			53)
		   (+ (abs (* (a) (b)))
                      (expt 2 (- 2 (expt 2 10)))))
	        (and (= (stk) 0) (= (grd) 0))))
  :hints (("Goal" :use (denorm-32
		        (:instance rnd-exactp-b (x (+ (abs (* (a) (b))) (expt 2 (- 2 (expt 2 10)))))
		                                (mode (modep))
						(n 53))))))

(local-defthmd denorm-34
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (iff (= (drnd (abs (* (a) (b))) (modep) (dp))
		   (abs (* (a) (b))))
	        (and (= (stk) 0) (= (grd) 0))))
  :hints (("Goal" :in-theory (enable drnd-rewrite dp expw bias spn)
                  :use (denorm-33 underflow-2))))

(defthmd drnd-equal
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (iff (= (drnd (* (a) (b)) (mode) (dp))
		   (* (a) (b)))
	        (and (= (stk) 0) (= (grd) 0))))
  :hints (("Goal" :use (denorm-34) :in-theory (enable drnd-modep-mode abs))))
