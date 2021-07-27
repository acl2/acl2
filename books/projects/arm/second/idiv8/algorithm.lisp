(in-package "RTL")

(include-book "loop")

(defund d () (* (expt 2 (- (clzb) 64)) (abs (b0))))

(defund x () (* (expt 2 (- (clza) 64)) (abs (a0))))

(in-theory (disable (x) (d)))

(defthm ratp-d
  (rationalp (d))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable d))))

(defthm ratp-x
  (rationalp (x))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable x))))

(defthmd d-expo-b
  (implies (not (earlyp))
	   (equal (d) (* (expt 2 (- (1+ (expo (b0))))) (abs (b0)))))
  :hints (("Goal" :in-theory (enable d clzb-rewrite)
	          :use (b0-rewrite b0<>0))))

(defthmd x-expo-a
  (implies (not (earlyp))
	   (equal (x) (* (expt 2 (- (1+ (expo (a0))))) (abs (a0)))))
  :hints (("Goal" :in-theory (enable x clza-rewrite)
	          :use (a0-rewrite b0<=a0 b0<>0))))

(defthmd d-sig-b
  (implies (not (earlyp))
	   (equal (d) (/ (sig (b0)) 2)))
  :hints (("Goal" :in-theory (enable d-expo-b)
                  :nonlinearp t
	          :use ((:instance fp-abs (x (b0)))))))

(defthmd x-sig-a
  (implies (not (earlyp))
	   (equal (x) (/ (sig (a0)) 2)))
  :hints (("Goal" :in-theory (enable x-expo-a)
                  :nonlinearp t
	          :use ((:instance fp-abs (x (a0)))))))

(defthmd d-bounds
  (implies (not (earlyp))
           (and (<= 1/2 (d))
	        (< (d) 1)))
  :hints (("Goal" :in-theory (enable d-sig-b)
                  :use (b0<>0
                        (:instance sig-lower-bound (x (b0)))
                        (:instance sig-upper-bound (x (b0))))
                  :nonlinearp t)))

(defthmd x-bounds
  (implies (not (earlyp))
           (and (<= 1/2 (x))
	        (< (x) 1)))
  :hints (("Goal" :in-theory (enable x-sig-a)
                  :use (b0<>0 b0<=a0
                        (:instance sig-lower-bound (x (a0)))
                        (:instance sig-upper-bound (x (a0))))
                  :nonlinearp t)))

(defund quotient (j)
  (if (zp j)
      0
    (+ (quotient (1- j))
       (* (expt 8 (- 1 j)) (q j)))))

(defund r (j)
  (* (expt 8 (1- j))
     (- (x) (* (d) (quotient j)))))

(in-theory (disable (quotient) (r)))
          
(defthmd r0-rewrite
  (equal (r 0) (/ (x) 8))
  :hints (("Goal" :in-theory (enable quotient r))))

(defthmd r-recurrence
  (implies (natp j)
           (equal (r (+ 1 j))
                  (- (* 8 (r j))
                     (* (q (1+ j)) (d)))))
  :hints (("Goal" :in-theory (enable r quotient))))

(defthmd r0-bound
  (implies (not (earlyp))
           (< (abs (r 0)) (* 4/7 (d))))
  :hints (("Goal" :in-theory (enable r0-rewrite)
           :use (x-bounds d-bounds))))

(defun m (k i)
  (- (* 1/64 (si (ag (+ k 3) (computecmpconst i)) 10))))

(in-theory (disable m (m)))

(defthm rat-m
  (implies (member k '(-3 -2 -1 0 1 2 3 4))
           (rationalp (m k i)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable m computecmpconst si))))

(defthm int-64-m
  (implies (member k '(-3 -2 -1 0 1 2 3 4))
           (integerp (* 64 (m k i))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable m computecmpconst si))))

(defthmd m-md8
  (implies (and (integerp k) (<= -3 k) (<= k 4)
                (bvecp i 6))
           (equal (m k i) (md8 k i)))
  :hints (("Goal" :in-theory (enable m md8 computecmpconst)
                  :use ((:instance bvecp-member (x i) (n 6))))))

(defund maxk (a)
  (cond ((<= (m 4 (bits (div) 65 60)) a) 4)
        ((<= (m 3 (bits (div) 65 60)) a) 3)
        ((<= (m 2 (bits (div) 65 60)) a) 2)
        ((<= (m 1 (bits (div) 65 60)) a) 1)
        ((<= (m 0 (bits (div) 65 60)) a) 0)
        ((<= (m -1 (bits (div) 65 60)) a) -1)
        ((<= (m -2 (bits (div) 65 60)) a) -2)
        ((<= (m -3 (bits (div) 65 60)) a) -3)
        (t -4)))

(defthmd div-rewrite
  (implies (not (earlyp))
           (equal (div) (* (expt 2 67) (d))))
  :hints (("Goal" :in-theory (enable bvecp div d absb-rewrite)
                  :nonlinearp t
                  :use (d-bounds b0<>0 clza<=clzb clza>=0))))

(defthmd div2-rewrite
  (implies (not (earlyp))
           (equal (div2) (* (expt 2 68) (d))))
  :hints (("Goal" :in-theory (enable bvecp div div2 d absb-rewrite)
                  :nonlinearp t
                  :use (d-bounds b0<>0 clza<=clzb clza>=0))))

(defthmd div3-rewrite
  (implies (not (earlyp))
           (equal (div3) (* 3 (expt 2 67) (d))))
  :hints (("Goal" :in-theory (enable bvecp div div2 div3 d absb-rewrite)
                  :nonlinearp t
                  :use (d-bounds b0<>0 clza<=clzb clza>=0))))

(defthmd div-bounds
  (implies (not (earlyp))
           (and (<= (expt 2 66) (div))
	        (< (div) (expt 2 67))))
  :hints (("Goal" :in-theory (enable div-rewrite)
                  :use (d-bounds)
		  :nonlinearp t)))

(defthmd div-bits-bounds
  (implies (not (earlyp))
           (and (<= (+ (expt 2 66) (* (expt 2 60) (bits (div) 65 60))) (div))
	        (< (div) (+ (expt 2 66) (* (expt 2 60) (1+ (bits (div) 65 60)))))))
  :hints (("Goal" :use (div-bounds
                        (:instance bitn-0-1 (x (div)) (n 66))
                        (:instance bitn-plus-bits (x (div)) (n 66) (m 0))
			(:instance bits-plus-bits (x (div)) (n 65) (p 60) (m 0))
			(:instance bits-bounds (x (div)) (i 65) (j 0))
			(:instance bits-bounds (x (div)) (i 59) (j 0)))
		  :in-theory (enable bvecp))))

(defthmd d-bits-bounds
  (implies (not (earlyp))
           (and (<= (+ 1/2 (/ (bits (div) 65 60) 128)) (d))
	        (< (d) (+ 1/2 (/ (1+ (bits (div) 65 60)) 128)))))
  :hints (("Goal" :use (div-bits-bounds)
                  :in-theory (enable div-rewrite)
		  :nonlinearp t)))

(defthmd bits-div-rewrite
  (implies (not (earlyp))
           (equal (bits (div) 65 60)
                  (fl (* 128 (- (d) 1/2)))))
  :hints (("Goal" :use (d-bits-bounds))))

(defthmd maxk-select-digit-d8
  (implies (and (not (earlyp)) (rationalp a))
           (equal (maxk a) (select-digit-d8 a (i64 (d)))))
  :hints (("Goal" :use (bits-div-rewrite) :in-theory (enable i64 maxk a select-digit-d8 m-md8))))

(defthmd q-vals
  (member (q j) '(-4 -3 -2 -1 0 1 2 3 4))
  :hints (("Goal" :in-theory (enable q-1 nextdigit)
                  :expand ((q j) (q 1)))))

(in-theory (disable (i64) (r$) (rho$)))

(defthmd r-bound-inv
  (implies (and (not (earlyp))
                (natp j)
                (<= (abs (r j)) (* 4/7 (d)))
                (rationalp approx)
                (integerp (* 64 approx))
                (< (abs (- approx (* 8 (r j)))) 1/64)
                (= (q (1+ j)) (maxk approx)))
	   (<= (abs (r (1+ j))) (* 4/7 (d))))
  :hints (("Goal" :use ((:functional-instance srt-div-rad-8
                         (e$ (lambda () (if (earlyp) (e$) 3)))
                         (d$ (lambda () (if (earlyp) (d$) (d))))
                         (x$ (lambda () (if (earlyp) (x$) (x))))
                         (a$ (lambda () (if (earlyp) (a$) 4)))
                         (q$ (lambda (j) (if (earlyp) (q$ j) (q j))))
                         (r$ (lambda () (if (earlyp) (r$) 8)))
                         (rho$ (lambda () (if (earlyp) (rho$) 4/7)))
                         (quot$ (lambda (j) (if (earlyp) (quot$ j) (quotient j))))
                         (rem$ (lambda (j) (if (earlyp) (rem$ j) (r j))))))
		  :in-theory (enable r r$ quotient quot$ rem$ rho$ maxk-select-digit-d8 bits-div-rewrite))		  
           ("Subgoal 12" :use (d-bounds))	   
	   ("Subgoal 11" :use (rho$-constraint))
	   ("Subgoal 10" :use (rho$-constraint e$-constraint a$-constraint))
	   ("Subgoal 9" :use (q-vals q$-constraint))
	   ("Subgoal 8" :use (q-vals q$-constraint a$-constraint d$-constraint x$-constraint x-bounds d-bounds))
	   ("Subgoal 7" :use (d$-constraint x$-constraint x-bounds d-bounds))
	   ("Subgoal 6" :use (d$-constraint x$-constraint x-bounds d-bounds))
	   ("Subgoal 8" :use (d$-constraint x$-constraint x-bounds d-bounds))
	   ("Subgoal 7" :use (d$-constraint x$-constraint x-bounds d-bounds))
	   ("Subgoal 6" :use (d$-constraint e$-constraint))
	   ("Subgoal 5" :use (d$-constraint e$-constraint))
	   ("Subgoal 2" :use (d$-constraint e$-constraint x$-constraint))))



