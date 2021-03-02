(in-package "RTL")

(include-book "rndbits")

(local-defthmd exprndinc-fracunrnd
  (implies (and (not (specialp))
                (= (exprndinc) 1))
           (equal (fracunrnd)
                  (1- (expt 2 52))))
  :hints (("Goal" :in-theory (enable bitn-bits exprndinc fracunrnd bvecp fracp1)
                  :use ((:instance bits-bounds (x (frac105)) (i 104) (j 53))
		        (:instance bits-bounds (x (fracp1)) (i 51) (j 0))
			(:instance bitn-plus-bits (x (fracp1)) (n 52) (m 0))))))

(local-defthmd expinc-case-1-0
  (implies (not (specialp))
           (< (prod) (- (expt 2 106) (expt 2 53))))
  :hints (("Goal" :in-theory (enable prod-rewrite sa sb bvecp)
                  :use (bvecp-mana bvecp-manb)
		  :nonlinearp t)))

(local-defthmd expinc-case-1-1
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (and (equal (bitn (prod) 105) 1)
	        (equal (rshift) 1)))
  :hints (("Goal" :in-theory (enable rexpinc))))

(local-defthmd expinc-case-1-2
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (frac105)
	          (bits (prod) 104 0)))
  :hints (("Goal" :in-theory (enable expinc-case-1-1 ash-rewrite cat prod0 rprodshft rfrac105)
                  :use ((:instance bits-shift-up-2 (x (bits (prod) 105 0)) (k 1) (i 105))))))

(local-defthmd expinc-case-1-3
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (bits (prod) 104 53)
	          (1- (expt 2 52))))
  :hints (("Goal" :use (exprndinc-fracunrnd) :in-theory (enable fracunrnd expinc-case-1-2))))

(local-defthmd expinc-case-1-4
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           (equal (bits (prod) 105 53)
	          (1- (expt 2 53))))
  :hints (("Goal" :in-theory (enable expinc-case-1-1 expinc-case-1-3)
                  :use ((:instance bitn-plus-bits (x (prod)) (n 105) (m 53))))))

(local-defthm expinc-case-1
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (<= (+ (ea) (eb) (1- (expt 2 10))) 0))
           ())
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expinc-case-1-4)
                  :use (expinc-case-1-0 bvecp-prod
		        (:instance bits-plus-bits (x (prod)) (n 105) (p 53) (m 0))
			(:instance bits-bounds (x (prod)) (i 52) (j 0))))))

(local-defthmd expinc-case-2-1
  (implies (not (specialp))
           (and (<= (sa) (1- (expt 2 53)))
	        (<= (sb) (1- (expt 2 53)))))
  :hints (("Goal" :in-theory (enable sa sb bvecp)
                  :use (bvecp-mana bvecp-manb))))

(local-defthmd expinc-case-2-2
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
                (= (expa) 0))
           (<= (sa) (1- (expt 2 (- 53 (clz*))))))
  :hints (("Goal" :in-theory (enable bvecp sa clz-expo clz-rewrite)
                  :use (expa-expb-0 bvecp-mana expa-0-mana
		        (:instance expo>= (x (mana)) (n 0))
		        (:instance expo-upper-bound (x (sa)))))))

(local-defthmd expinc-case-2-3
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
                (= (expb) 0))
           (<= (sb) (1- (expt 2 (- 53 (clz*))))))
  :hints (("Goal" :in-theory (enable bvecp sb clz-expo clz-rewrite)
                  :use (expa-expb-0 bvecp-manb expb-0-manb
		        (:instance expo>= (x (manb)) (n 0))
		        (:instance expo-upper-bound (x (sb)))))))

(local-defthmd natp-s
  (implies (not (specialp))
           (and (natp (sa)) (natp (sb))))
  :hints (("Goal" :in-theory (enable bvecp sa sb)
                  :use (bvecp-mana bvecp-manb))))
		  
(local-defthmd expinc-case-2-4
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0))
           (<= (prod) (* (1- (expt 2 53)) (1- (expt 2 (- 53 (clz*)))))))
  :hints (("Goal" :in-theory (enable prod-rewrite clz-rewrite)
                  :nonlinearp t
                  :use (natp-s expa-expb-0 expinc-case-2-1 expinc-case-2-2 expinc-case-2-3))))

(local-defthmd expinc-case-2-5
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (< (lprodshft) (- (expt 2 106) (expt 2 53))))
  :hints (("Goal" :in-theory (enable case-2-13)
                  :nonlinearp t
                  :use (expinc-case-2-4 clz-bounds))))

(local-defthmd expinc-case-2-6
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (bits (lprodshft) 104 53)
	          (1- (expt 2 52))))
  :hints (("Goal" :in-theory (enable case-2-28 fracunrnd)
                  :use (exprndinc-fracunrnd))))

(local-defthm expinc-case-2-7
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (>= (bits (lprodshft) 104 0)
	       (- (expt 2 105) (expt 2 53))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expinc-case-2-6)
                  :use ((:instance bits-plus-bits (x (lprodshft)) (n 104) (p 53) (m 0))
		        (:instance bits-bounds (x (lprodshft)) (i 52) (j 0))))))

(local-defthm expinc-case-2-8
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(> (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           ())
  :rule-classes ()
  :hints (("Goal" :use (expinc-case-2-5 expinc-case-2-7 case-2-29))))

(local-defthmd expinc-case-2-9
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (< (lprodshft) (- (expt 2 105) (expt 2 52))))
  :hints (("Goal" :in-theory (enable case-2-37)
                  :nonlinearp t
                  :use (expinc-case-2-4 clz-bounds))))

(local-defthmd expinc-case-2-10
  (implies (and (not (specialp))
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (frac105)
	          (bits (* 2 (lprodshft)) 104 0)))
  :hints (("Goal" :in-theory (enable ash-rewrite bvecp)
                  :use (case-2-46
		        (:instance bits-shift-up-2 (x (lprodshft)) (k 1) (i 103))
		        (:instance expo-upper-bound (x (lprodshft)))))))

(local-defthmd expinc-case-2-11
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           (equal (bits (lprodshft) 103 52)
	          (1- (expt 2 52))))
  :hints (("Goal" :in-theory (enable expinc-case-2-10 ash-rewrite bvecp)
                  :use (exprndinc-fracunrnd fracunrnd
		        (:instance bits-shift-up-1 (x (lprodshft)) (k 1) (i 104) (j 53))))))

(local-defthm expinc-case-2-12
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(= (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           ())
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expinc-case-2-11)
                  :use (expinc-case-2-9 case-2-49
		        (:instance bits-plus-bits (x (lprodshft)) (n 103) (p 52) (m 0))
		        (:instance bits-bounds (x (lprodshft)) (i 51) (j 0))))))

(local-defthm expinc-case-2-13
  (implies (and (not (specialp))
		(= (expinc) 1)
		(= (exprndinc) 1)
                (> (+ (ea) (eb) (1- (expt 2 10))) 0)
		(< (+ (ea) (eb) (1- (expt 2 10))) (clz*)))
           ())
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lexpinc expdiffbiasedzero-rewrite case-2-71))))

(defthmd expinc-exprndinc
  (implies (and (not (specialp))
		(= (expinc) 1))
           (equal (exprndinc) 0))
  :hints (("Goal" :in-theory (enable exprndinc)
                  :use (expinc-case-1 expinc-case-2-8 expinc-case-2-12 expinc-case-2-13))))
		  
