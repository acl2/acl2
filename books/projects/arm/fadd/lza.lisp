(in-package "RTL")

(include-book "clz")

(defund in1lzap () (1+ (in1lza)))

(defund lzap () (lza128 (in1lzap) (in2lza)))

(in-theory (disable (in1lzap) (lzap)))

(defund pp () (logxor (in1lzap) (in2lza)))

(defund kp ()
  (logand (bits (lognot (in1lzap)) 127 0)
          (bits (lognot (in2lza)) 127 0)))

(defund w0p () (bits (lognot (logxor (pp) (ash (kp) 1))) 127 0))

(local-defthmd bvecp-w0p
  (bvecp (w0p) 128)
  :hints (("Goal" :in-theory (enable w0p))))

(defthmd lzap128-lemma
  (equal (lzap) (clz (bits (ash (w0p) (- 1)) 127 0)))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(lza128 lzap pp kp w0p))))

(local-in-theory (disable (in1lzap) (lzap) (pp) (kp) (w0p)))

(local-defthmd pp-rewrite
  (implies (and (natp j) (< j 128))
           (equal (bitn (pp) j)
	          (if (= (bitn (in1lzap) j) (bitn (in2lza) j))
                      0 1)))
  :hints (("Goal" :in-theory (enable pp bitn-logxor)
                  :use ((:instance bitn-0-1 (n j) (x (in1lzap)))
			(:instance bitn-0-1 (n j) (x (in2lza)))))))

(local-defthmd kp-rewrite
  (implies (and (natp j) (< j 128))
           (equal (bitn (kp) j)
	          (if (and (= (bitn (in1lzap) j) 0) (= (bitn (in2lza) j) 0))
                      1 0)))
  :hints (("Goal" :in-theory (enable kp bitn-bits bitn-logand)
                  :use ((:instance bitn-0-1 (n j) (x (in1lzap)))
			(:instance bitn-0-1 (n j) (x (in2lza)))
			(:instance bitn-0-1 (n j) (x (lognot (in1lzap))))
			(:instance bitn-0-1 (n j) (x (lognot (in2lza))))
			(:instance bitn-lognot (n j) (x (in1lzap)))
			(:instance bitn-lognot (n j) (x (in2lza)))))))

(local-defthmd w0p-rewrite
  (implies (and (not (zp j)) (< j 128))
           (equal (bitn (w0p) j)
	          (if (= (bitn (pp) j) (bitn (kp) (1- j)))
                      1 0)))
  :hints (("Goal" :in-theory (enable w0p bitn-bits bitn-logxor bitn-logand)
                  :use ((:instance bitn-0-1 (n j) (x (pp)))
			(:instance bitn-0-1 (n (1- j)) (x (kp)))
			(:instance bitn-0-1 (n j) (x (lognot (LOGXOR (PP) (* 2 (KP))))))
			(:instance bitn-lognot (x (LOGXOR (PP) (* 2 (KP)))) (n j))
			(:instance bitn-shift-up (x (kp)) (k 1) (n (1- j)))))))


(defund s0p () (+ (in1lzap) (in2lza)))

(local-defund assumps ()
  (and (bvecp (in1lzap) 128)
       (bvecp (in2lza) 128)
       (> (s0p) (expt 2 128))))

(local-defund conds (j)
  (and (= (bits (w0p) 127 (1+ j)) 0)
       (= (bits (s0p) 127 (1+ j)) 0)
       (or (>= (+ (bits (in1lzap) j 0) (bits (in2lza) j 0)) (expt 2 (1+ j)))
           (= (bitn (kp) j) 1))))

(local-defund goal ()
  (and (>= (w0p) 2)
       (or (= (expo (bits (s0p) 127 0)) (expo (w0p)))
           (= (expo (bits (s0p) 127 0)) (1- (expo (w0p)))))))

(local-in-theory (disable (s0p) (assumps) (conds) (goal)))

(local-defthm conds-127
  (implies (assumps) (conds 127))
  :hints (("Goal" :in-theory (enable assumps conds s0p))))

(local-defthmd s-127-0
  (implies (assumps)
           (not (equal (bits (s0p) 127 0) 0)))
  :hints (("Goal" :in-theory (enable s0p assumps bvecp)
                  :use ((:instance bitn-plus-bits (x (s0p)) (n 128) (m 0))))))

(local-defthmd conds-0-1
  (implies (and (assumps) (conds 0))
           (equal (bitn (s0p) 0) 1))
  :hints (("Goal" :in-theory (enable assumps conds s0p)
                 :use (s-127-0
		       (:instance bitn-0-1 (x (s0p)) (n 0))
                       (:instance bits-plus-bitn (x (s0p)) (n 127) (m 0))))))

(local-defthmd conds-0-2
  (implies (and (assumps) (conds 0))
           (equal (bitn (s0p) 0)
	          (mod (+ (bitn (in1lzap) 0) (bitn (in2lza) 0)) 2)))
  :hints (("Goal" :in-theory (enable s0p bitn-rec-0)
                  :use ((:instance mod-sum (n 2) (a (in1lzap)) (b (in2lza)))
		        (:instance mod-sum (n 2) (b (in1lzap)) (a (mod (in2lza) 2)))))))

(local-defthm conds-0
  (implies (assumps) (not (conds 0)))
  :hints (("Goal" :in-theory (enable conds kp-rewrite)
                  :use (conds-0-1 conds-0-2
                        (:instance bitn-0-1 (n 0) (x (in1lzap)))
			(:instance bitn-0-1 (n 0) (x (in2lza)))))))

(local-defthmd w0p-1-1
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 1))
           (equal (expo (w0p)) j))
  :hints (("Goal" :in-theory (enable conds bvecp)
                  :nonlinearp t
                  :use (bvecp-w0p
                        (:instance expo>= (x (w0p)) (n j))
			(:instance expo<= (x (w0p)) (n j))
			(:instance bitn-plus-bits (x (w0p)) (n j) (m 0))
			(:instance bits-plus-bits (x (w0p)) (n 127) (p (1+ j)) (m 0))
			(:instance bits-bounds (x (w0p)) (i (1- j)) (j 0))))))

(local-defthmd w0p-1-2
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 1))
           (equal (bitn (pp) j) (bitn (kp) (1- j))))
  :hints (("Goal" :in-theory (enable w0p-rewrite))))

(local-defthmd w0p-1-3
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 1))
           (not (= (bitn (pp) j) 1)))
  :hints (("Goal" :use (w0p-1-2
                        (:instance bitn-0-1 (x (in1lzap)) (n j))
                        (:instance bitn-0-1 (x (in2lza)) (n j))
                        (:instance bitn-0-1 (x (in1lzap)) (n (1- j)))
                        (:instance bitn-0-1 (x (in2lza)) (n (1- j)))
			(:instance bitn-plus-bits (x (in1lzap)) (n j) (m 0))
			(:instance bitn-plus-bits (x (in2lza)) (n j) (m 0))
			(:instance bitn-plus-bits (x (in1lzap)) (n (1- j)) (m 0))
			(:instance bitn-plus-bits (x (in2lza)) (n (1- j)) (m 0))
			(:instance bits-bounds (x (in1lzap)) (i (- j 2)) (j 0))
			(:instance bits-bounds (x (in2lza)) (i (- j 2)) (j 0)))
                  :in-theory (enable conds pp-rewrite kp-rewrite)
		  :nonlinearp t)))

(local-defthmd w0p-1-4
  (implies (natp j)
           (equal (bits (s0p) j 0)
                  (mod (+ (bits (in1lzap) j 0) (bits (in2lza) j 0)) (expt 2 (1+ j)))))
  :hints (("Goal" :in-theory (enable s0p bits-mod)
                  :use ((:instance mod-sum (n (expt 2 (1+ j))) (a (in1lzap)) (b (in2lza)))
		        (:instance mod-sum (n (expt 2 (1+ j))) (b (in1lzap)) (a (mod (in2lza) (expt 2 (1+ j)))))))))
   
(local-defthmd w0p-1-5
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 1) (= (bitn (pp) j) 0))
           (equal (bits (s0p) j 0)
	          (+ (bits (in1lzap) (1- j) 0) (bits (in2lza) (1- j) 0))))
  :hints (("Goal" :use ((:instance bitn-0-1 (x (in1lzap)) (n j))
                        (:instance bitn-0-1 (x (in2lza)) (n j))
			(:instance bitn-plus-bits (x (in1lzap)) (n j) (m 0))
			(:instance bitn-plus-bits (x (in2lza)) (n j) (m 0))
			(:instance bits-bounds (x (in1lzap)) (i (1- j)) (j 0))
			(:instance bits-bounds (x (in2lza)) (i (1- j)) (j 0)))
                  :in-theory (enable w0p-1-4 pp-rewrite)
		  :nonlinearp t)))

(local-defthmd w0p-1-6
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 1) (= (bitn (pp) j) 0))
           (equal (bits (s0p) 127 0)
	          (+ (bits (in1lzap) (1- j) 0) (bits (in2lza) (1- j) 0))))
  :hints (("Goal" :use ((:instance bits-plus-bits (x (s0p)) (n 127) (p (1+ j)) (m 0)))
                  :in-theory (enable w0p-1-5 conds))))

(local-defthmd w0p-1-7
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 1) (= (bitn (pp) j) 0))
           (and (>= (expo (bits (s0p) 127 0)) (1- j))
	        (<= (expo (bits (s0p) 127 0)) j)))
  :hints (("Goal" :use ((:instance bitn-0-1 (x (in1lzap)) (n j))
                        (:instance bitn-0-1 (x (in2lza)) (n j))
			(:instance bitn-0-1 (x (in1lzap)) (n (1- j)))
                        (:instance bitn-0-1 (x (in2lza)) (n (1- j)))
			(:instance bitn-plus-bits (x (in1lzap)) (n (1- j)) (m 0))
			(:instance bitn-plus-bits (x (in2lza)) (n (1- j)) (m 0))
			(:instance bits-bounds (x (in1lzap)) (i (- j 2)) (j 0))
			(:instance bits-bounds (x (in2lza)) (i (- j 2)) (j 0))
			(:instance expo>= (x (bits (s0p) 127 0)) (n (1- j)))
			(:instance expo<= (x (bits (s0p) 127 0)) (n j)))
		  :nonlinearp t
                  :in-theory (enable w0p-1-6 w0p-rewrite pp-rewrite kp-rewrite))))

(local-defthmd w0p-1
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 1))
           (goal))
  :hints (("Goal" :use (w0p-1-3 w0p-1-7
                        (:instance bvecp-bitn-0 (x (w0p)) (n j))
                        (:instance bitn-0-1 (x (pp)) (n j)))
		  :nonlinearp t
                  :in-theory (e/d (bvecp goal w0p-1-1) (bvecp-bitn-0)))))

(local-defthmd w0p-0-1
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0))
           (equal (bits (w0p) 127 j) 0))
  :hints (("Goal" :use ((:instance bits-plus-bitn (x (w0p)) (n 127) (m j)))
                  :in-theory (enable conds))))

(local-defthmd w0p-0-2
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0) (= (bitn (pp) j) 1))
           (>= (+ (bits (in1lzap) (1- j) 0) (bits (in2lza) (1- j) 0))
	       (expt 2 j)))
  :hints (("Goal" :use ((:instance bits-plus-bitn (x (w0p)) (n 127) (m j))
                        (:instance bitn-plus-bits (x (in1lzap)) (n j) (m 0))
                        (:instance bitn-plus-bits (x (in2lza)) (n j) (m 0))
			(:instance bitn-0-1 (x (in1lzap)) (n j))
			(:instance bitn-0-1 (x (in2lza)) (n j)))
		  :nonlinearp t
                  :in-theory (enable conds pp-rewrite kp-rewrite))))

(local-defthm w0p-0-3
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0))
           (or (= (bitn (kp) (1- j)) 1)
	       (>= (+ (bits (in1lzap) (1- j) 0) (bits (in2lza) (1- j) 0))
                   (expt 2 j))))
  :rule-classes ()
  :hints (("Goal" :use (w0p-0-2)
                  :in-theory (enable conds pp-rewrite kp-rewrite w0p-rewrite))))

(local-defthm w0p-0-4
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0))
           (or (= (bitn (kp) (1- j)) 1)
	       (>= (+ (bits (in1lzap) (1- j) 0) (bits (in2lza) (1- j) 0))
                   (expt 2 j))))
  :rule-classes ()
  :hints (("Goal" :use (w0p-0-2)
                  :in-theory (enable conds pp-rewrite kp-rewrite w0p-rewrite))))

(in-theory (disable ACL2::|(mod (+ x y) z) where (<= 0 z)|))

(local-defthmd w0p-0-5
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0) (= (bitn (pp) j) 1))
           (equal (bits (s0p) j 0)
	          (mod (+ (expt 2 j) (bits (in1lzap) (1- j) 0) (bits (in2lza) (1- j) 0))
		       (expt 2 (1+ j)))))
  :hints (("Goal" :use (w0p-0-2
                        (:instance bitn-plus-bits (x (in1lzap)) (n j) (m 0))
                        (:instance bitn-plus-bits (x (in2lza)) (n j) (m 0))
                        (:instance bitn-0-1 (x (in1lzap)) (n j))
                        (:instance bitn-0-1 (x (in2lza)) (n j)))
                  :in-theory (enable w0p-1-4 pp-rewrite))))

(local-defthmd w0p-0-6
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0) (= (bitn (pp) j) 1))
           (equal (bits (s0p) j 0)
                  (mod (- (+ (bits (in1lzap) (1- j) 0) (bits (in2lza) (1- j) 0)) (expt 2 j)) (expt 2 (1+ j)))))
  :hints (("Goal" :use ((:instance mod-mult (m (- (+ (bits (in1lzap) (1- j) 0) (bits (in2lza) (1- j) 0)) (expt 2 j)))
			                    (n (expt 2 (1+ j)))
					    (a 1)))
		  ;:nonlinearp t
                  :in-theory (enable w0p-0-5 w0p-rewrite pp-rewrite kp-rewrite))))

(local-defthm w0p-0-7
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0) (= (bitn (pp) j) 1))
           (< (bits (s0p) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use (w0p-0-2
			(:instance bits-bounds (x (in1lzap)) (i (1- j)) (j 0))
			(:instance bits-bounds (x (in2lza)) (i (1- j)) (j 0)))
		  :nonlinearp t
                  :in-theory (enable w0p-0-6))))

(local-defthm w0p-0-8
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0) (= (bitn (pp) j) 0) (= (bitn (kp) j) 1))
           (< (bits (s0p) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-0-1 (x (in1lzap)) (n j))
                        (:instance bitn-0-1 (x (in2lza)) (n j))
			(:instance bitn-0-1 (x (in1lzap)) (n (1- j)))
                        (:instance bitn-0-1 (x (in2lza)) (n (1- j)))
                        (:instance bitn-plus-bits (x (in1lzap)) (n j) (m 0))
                        (:instance bitn-plus-bits (x (in2lza)) (n j) (m 0))
                        (:instance bitn-plus-bits (x (in1lzap)) (n (1- j)) (m 0))
                        (:instance bitn-plus-bits (x (in2lza)) (n (1- j)) (m 0))
			(:instance bits-bounds (x (in1lzap)) (i (- j 2)) (j 0))
			(:instance bits-bounds (x (in2lza)) (i (- j 2)) (j 0)))
		  :nonlinearp t
                  :in-theory (enable w0p-1-4 w0p-rewrite pp-rewrite kp-rewrite))))

(local-defthm w0p-0-9
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0) (= (bitn (pp) j) 0) (= (bitn (kp) j) 0))
           (< (bits (s0p) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bitn-0-1 (x (in1lzap)) (n j))
                        (:instance bitn-0-1 (x (in2lza)) (n j))
			(:instance bitn-0-1 (x (in1lzap)) (n (1- j)))
                        (:instance bitn-0-1 (x (in2lza)) (n (1- j)))
                        (:instance bitn-plus-bits (x (in1lzap)) (n j) (m 0))
                        (:instance bitn-plus-bits (x (in2lza)) (n j) (m 0))
                        (:instance bitn-plus-bits (x (in1lzap)) (n (1- j)) (m 0))
                        (:instance bitn-plus-bits (x (in2lza)) (n (1- j)) (m 0))
			(:instance bits-bounds (x (in1lzap)) (i (- j 2)) (j 0))
			(:instance bits-bounds (x (in2lza)) (i (- j 2)) (j 0)))
		  :nonlinearp t
                  :in-theory (enable w0p-1-4 w0p-rewrite pp-rewrite kp-rewrite))))

(local-defthm w0p-0-10
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0))
           (< (bits (s0p) j 0) (expt 2 j)))
  :rule-classes ()
  :hints (("Goal" :use (w0p-0-7 w0p-0-8 w0p-0-9)
                  :in-theory (enable pp-rewrite kp-rewrite))))

(local-defthm w0p-0-11
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0))
           (equal (bitn (s0p) j) 0))
  :hints (("Goal" :use (w0p-0-10
                        (:instance bitn-0-1 (x (s0p)) (n j))
                        (:instance bitn-plus-bits (x (s0p)) (n j) (m 0))))))

(local-defthm w0p-0-12
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0))
           (equal (bits (s0p) 127 j) 0))
  :hints (("Goal" :use ((:instance bits-plus-bitn (x (s0p)) (n 127) (m j)))
                  :in-theory (enable conds w0p-0-11))))

(local-defthmd w0p-0
  (implies (and (not (zp j)) (< j 128) (conds j) (= (bitn (w0p) j) 0))
           (conds (1- j)))
  :hints (("Goal" :use (w0p-0-1 w0p-0-4 w0p-0-12)
                  :in-theory (enable conds))))

(local-defthm conds-goal
  (implies (and (natp j) (< j 128) (conds j) (assumps))
           (goal))	   
  :rule-classes ()
  :hints (("Goal" :induct (nats j))
          ("Subgoal *1/2" :use (w0p-1 w0p-0 (:instance bitn-0-1 (x (w0p)) (n j))))))

(local-defthm assumps-goal
  (implies (assumps) (goal))	   
  :rule-classes ()
  :hints (("Goal" :use ((:instance conds-goal (j 127))))))

(local-defthm expo-s0p-1
  (implies (and (rationalp x) (>= x 2))
           (and (< (/ x 2) (expt 2 (expo x)))
	        (<= (expt 2 (1- (expo x))) (/ x 2))
		(>= (expo x) 1)))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t
                  :use (expo-lower-bound expo-upper-bound (:instance expo>= (n 1))))))

(local-defthm expo-s0p-2
  (implies (and (rationalp x) (>= x 2))
           (and (< (fl (/ x 2)) (expt 2 (expo x)))
	        (<= (expt 2 (1- (expo x))) (fl (/ x 2)))
		(>= (expo x) 1)))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t
                  :use (expo-s0p-1
		        (:instance fl-def (x (/ x 2)))
			(:instance n<=fl-linear (n (expt 2 (1- (expo x)))) (x (/ x 2)))))))

(local-defthm expo-s0p-3
  (implies (and (rationalp x) (>= x 2))
           (equal (expo (fl (* 1/2 x)))
	          (1- (expo x))))
  :hints (("Goal" :use (expo-s0p-2 (:instance expo-unique (x (fl (* 1/2 x))) (n (1- (expo x))))))))

(local-defthm expo-s0p-4
  (implies (>= (w0p) 2)
           (equal (expo (w0p))
                  (1+ (expo (bits (ash (w0p) (- 1)) 127 0)))))
  :hints (("Goal" :nonlinearp t
                  :use ((:instance bits-bounds (x (LOGNOT (LOGXOR (PP) (* 2 (KP))))) (i 127) (j 0)))
                  :in-theory (enable w0p bvecp))))

(local-defthm expo-s0p-5
  (implies (>= (w0p) 2)
           (>= (bits (ash (w0p) (- 1)) 127 0) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable w0p bvecp)
                  :use ((:instance expo-s0p-2 (x (BITS (LOGNOT (LOGXOR (PP) (* 2 (KP)))) 127 0)))
		        (:instance bits-bounds (x (LOGNOT (LOGXOR (PP) (* 2 (KP))))) (i 127) (j 0))))))

(local-defthm expo-s0p-6
  (<= (expo (w0p)) 127)
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-bounds (x (lognot (logxor (pp) (ash (kp) 1)))) (i 127) (j 0))
                        (:instance expo<= (x (w0p)) (n 127)))
	          :in-theory (enable w0p))))

(local-defthm expo-s0p-7
  (implies (>= (w0p) 2)
           (<= (expo (bits (ash (w0p) (- 1)) 127 0))
               126))
  :rule-classes ()
  :hints (("Goal" :use (expo-s0p-6))))

(local-defthm expo-s0p
  (implies (and (bvecp (in1lzap) 128)
                (bvecp (in2lza) 128)
                (> (s0p) (expt 2 128)))
           (and (> (lzap) 0)
                   (or (= (expo (bits (s0p) 127 0)) (- 127 (lzap)))
                       (= (expo (bits (s0p) 127 0)) (- 128 (lzap))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable lzap128-lemma assumps goal lzcnt-expo clz-expo)
                  :use (expo-s0p-5 expo-s0p-7 assumps-goal))))

(local-defthmd expo-sum-lzap-1
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (expdiff) (abs (- (expa) (expb)))))
  :hints (("Goal" :in-theory (enable opbgeopa far-rewrite expdiff-rewrite exps))))

(local-defthmd expo-sum-lzap-2
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (abs (- (expa) (expb)))
	          (if (= (bitn (expa) 0) (bitn (expb) 0))
		      0 1)))
  :hints (("Goal" :in-theory (enable opbgeopa far-rewrite bitn-rec-0 exps)
                  :use ((:instance mod-plus-mod-2 (a (exps)) (b 1))))))

(local-defthmd expo-sum-lzap-3
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (expdiff)
	          (if (= (bitn (expa) 0) (bitn (expb) 0))
		      0 1)))
  :hints (("Goal" :use (expo-sum-lzap-1 expo-sum-lzap-2))))

(local-defthm expo-sum-lzap-4
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (mulstk) 0))
  :hints (("Goal" :use (expb-pos-b) :in-theory (enable exps))))

(local-defthmd expo-sum-lzap-5
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (sum) (- (sigl) (* (expt 2 (- (expdiff))) (sigs)))))
  :hints (("Goal" :use (near-shiftout-0 sum-usa-27) :in-theory (enable far-rewrite))))

(local-defthm expo-sum-lzap-6
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (stk) 0))
  :hints (("Goal" :use (near-shiftout-0) :in-theory (enable stk* add-lemma))))

(defthm expo-sum-lzap-7
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (>= (sum) 1))
  :rule-classes ()
  :hints (("Goal" :use (a+b<>0 sum-bounds-0) :in-theory (enable exps absval))))

(local-defthmd expo-sum-lzap-8
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (in1lza) (* (expt 2 21) (sigl))))
  :hints (("Goal" :in-theory (enable exps siga sigb sigl in1lza fracl opbgeopa cat fraca fracb frac bvecp)
                  :use ((:instance bits-bounds (x (fracl)) (i 104) (j 0))))))

(defthmd in1lza-rewrite
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0) (= (expa) (expb)))
           (equal (in2lza) (- (expt 2 128) (1+ (* (expt 2 21) (sigs))))))
  :hints (("Goal" :in-theory (enable bits-lognot exps siga sigb sigs in2lza fracs opbgeopa cat fraca fracb frac bvecp)
                  :use ((:instance bits-bounds (x (fracs)) (i 104) (j 0))))))

(local-defthmd expo-sum-lzap-10
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0) (= (abs (- (expa) (expb))) 1))
           (equal (in2lza) (- (expt 2 128) (1+ (* (expt 2 20) (sigs))))))
  :hints (("Goal" :in-theory (enable bits-lognot exps siga sigb sigs in2lza fracs opbgeopa cat fraca fracb frac bvecp)
                  :use (expo-sum-lzap-2 (:instance bits-bounds (x (fracs)) (i 104) (j 0))))))

(defthmd in2lza-rewrite
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (in2lza) (- (expt 2 128) (1+ (* (expt 2 (- 21 (expdiff))) (sigs))))))
  :hints (("Goal" :use (in1lza-rewrite expo-sum-lzap-10) :in-theory (enable far-rewrite expo-sum-lzap-1))))

(defthmd sum-lza
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (+ (in1lza) (in2lza)) (+ (expt 2 128) (1- (* (expt 2 21) (sum))))))
  :hints (("Goal" :in-theory (enable expo-sum-lzap-5 expo-sum-lzap-8 in2lza-rewrite))))

(local-defthmd expo-sum-lzap-13
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (s0p) (+ (expt 2 128) (* (expt 2 21) (sum)))))
  :hints (("Goal" :in-theory (enable s0p in1lzap) :use (sum-lza))))

(local-defthmd expo-sum-lzap-14
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (and (bvecp (in1lzap) 128) (bvecp (in2lza) 128)))
  :hints (("Goal" :in-theory (enable in1lzap in1lza in2lza bits-lognot bvecp cat)
                  :use ((:instance bits-bounds (x (fracs)) (i 104) (j 0))
		        (:instance bits-bounds (x (fracl)) (i 104) (j 0))))))

(local-defthm expo-sum-lzap-15
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (and (> (lzap) 0)
                   (or (= (expo (bits (s0p) 127 0)) (- 127 (lzap)))
                       (= (expo (bits (s0p) 127 0)) (- 128 (lzap))))))
  :rule-classes ()
  :hints (("Goal" :use (expo-s0p expo-sum-lzap-7)
                  :in-theory (enable expo-sum-lzap-13 expo-sum-lzap-14))))

(local-defthm expo-sum-lzap-16
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (and (>= (* (expt 2 21) (sum)) (expt 2 21))
	        (< (* (expt 2 21) (sum)) (expt 2 128))))
  :rule-classes ()
  :hints (("Goal" :use (bvecp-siga bvecp-sigb expo-sum-lzap-7)
                  :nonlinearp t
		  :in-theory (enable expo-sum-lzap-5 bvecp sigl sigs))))

(local-defthm expo-sum-lzap-17
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (bits (s0p) 127 0) (* (expt 2 21) (sum))))
  :hints (("Goal" :use (expo-sum-lzap-16
                        (:instance mod-mult (m (* (expt 2 21) (sum))) (a 1) (n (expt 2 128))))
                  :in-theory (enable expo-sum-lzap-13 bits-mod))))

(defthm expo-sum-lzap
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (or (= (expo (sum)) (- 106 (lzap)))
               (= (expo (sum)) (- 107 (lzap)))))
  :rule-classes ()
  :hints (("Goal" :use (expo-sum-lzap-7 expo-sum-lzap-15 (:instance expo-shift (x (sum)) (n 21)))
                  :nonlinearp t
		  :in-theory (enable expo-shift))))

(local-defthmd in1lza-in1lzap-1
  (equal (fl (/ (in1lza) 2))
         (fl (/ (in1lzap) 2)))
  :hints (("Goal" :in-theory (enable cat in1lza in1lzap fracl fraca fracb bvecp)
                  :use ((:instance bits-bounds (x (fracl)) (i 104) (j 0))))))

(defthm bitn-in1lza-in1lzap
  (implies (not (zp k))
           (equal (bitn (in1lzap) k)
	          (bitn (in1lza) k)))
  :hints (("Goal" :use (in1lza-in1lzap-1
                        (:instance bitn-rec-pos (x (in1lza)) (n k))
			(:instance bitn-rec-pos (x (in1lzap)) (n k))))))

(local-defthmd p-rewrite
  (implies (and (natp j) (< j 128))
           (equal (bitn (p) j)
	          (if (= (bitn (in1lza) j) (bitn (in2lza) j))
                      0 1)))
  :hints (("Goal" :in-theory (enable p bitn-logxor)
                  :use ((:instance bitn-0-1 (n j) (x (in1lza)))
			(:instance bitn-0-1 (n j) (x (in2lza)))))))

(local-defthmd k-rewrite
  (implies (and (natp j) (< j 128))
           (equal (bitn (k) j)
	          (if (and (= (bitn (in1lza) j) 0) (= (bitn (in2lza) j) 0))
                      1 0)))
  :hints (("Goal" :in-theory (enable k bitn-bits bitn-logand)
                  :use ((:instance bitn-0-1 (n j) (x (in1lza)))
			(:instance bitn-0-1 (n j) (x (in2lza)))
			(:instance bitn-0-1 (n j) (x (lognot (in1lza))))
			(:instance bitn-0-1 (n j) (x (lognot (in2lza))))
			(:instance bitn-lognot (n j) (x (in1lza)))
			(:instance bitn-lognot (n j) (x (in2lza)))))))

(local-defthmd w0-rewrite
  (implies (and (not (zp j)) (< j 128))
           (equal (bitn (w0) j)
	          (if (= (bitn (p) j) (bitn (k) (1- j)))
                      1 0)))
  :hints (("Goal" :in-theory (enable w0 bitn-bits bitn-logxor bitn-logand)
                  :use ((:instance bitn-0-1 (n j) (x (p)))
			(:instance bitn-0-1 (n (1- j)) (x (k)))
			(:instance bitn-0-1 (n j) (x (lognot (LOGXOR (P) (* 2 (K))))))
			(:instance bitn-lognot (x (LOGXOR (P) (* 2 (K)))) (n j))
			(:instance bitn-shift-up (x (k)) (k 1) (n (1- j)))))))

(defthmd bitn-w0-w0p-low
  (implies (and (natp k) (>= k 2) (< k 128))
           (equal (bitn (w0p) k)
	          (bitn (w0) k)))
  :hints (("Goal" :in-theory (enable w0-rewrite w0p-rewrite p-rewrite pp-rewrite k-rewrite kp-rewrite))))

(defthmd bitn-w0-0
  (implies (and (natp k) (>= k 128))
           (equal (bitn (w0) k) 0))
  :hints (("Goal" :in-theory (enable w0 bvecp))))

(defthmd bitn-w0p-0
  (implies (and (natp k) (>= k 128))
           (equal (bitn (w0p) k) 0))
  :hints (("Goal" :in-theory (enable w0p bvecp))))

(local-defthmd bitn-w0-w0p
  (implies (and (natp k) (>= k 2))
           (equal (bitn (w0p) k)
	          (bitn (w0) k)))
  :hints (("Goal" :in-theory (enable bitn-w0-0 bitn-w0p-0 bitn-w0-w0p-low)
                  :cases ((< k 128)))))

(local-defund fw () (bits (ash (w0) (- 1)) 127 0))

(local-defund fwp () (bits (ash (w0p) (- 1)) 127 0))

(local-in-theory (disable (fw) (fwp)))

(local-defthm bitn-fw-0
  (implies (and (natp k) (>= k 128))
           (equal (bitn (fw) k) 0))
  :hints (("Goal" :in-theory (enable bvecp fw))))

(local-defthm bitn-fwp-0
  (implies (and (natp k) (>= k 128))
           (equal (bitn (fwp) k) 0))
  :hints (("Goal" :in-theory (enable bvecp fwp))))

(local-defthm bitn-fw-fwp-low
  (implies (and (not (zp k)) (< k 128))
           (equal (bitn (fwp) k) (bitn (fw) k)))
  :hints (("Goal" :in-theory (enable fw fwp bitn-w0-w0p bitn-bits)
                  :use ((:instance bitn-rec-pos (x (w0)) (n (1+ k)))
		        (:instance bitn-rec-pos (x (w0p)) (n (1+ k)))))))

(local-defthm bitn-fw-fwp
  (implies (not (zp k))
           (equal (bitn (fwp) k) (bitn (fw) k)))
  :hints (("Goal" :cases ((< k 128)))))

(local-defthmd expo-fwp-lzap
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (expo (fwp)) (- 127 (lzap))))
  :hints (("Goal" :in-theory (enable fwp lzap128-lemma clz-expo))))

(local-defthmd expo-fwp-bound
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (>= (expo (fwp)) 20))
  :hints (("Goal" :in-theory (enable expo-fwp-lzap)
                  :use (expo-sum-lzap expo-sum-lzap-7 (:instance expo>= (x (sum)) (n 0))))))

(defthmd bitn-expo
  (implies (not (zp x))
           (equal (bitn x (expo x)) 1))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (expo-upper-bound expo-lower-bound
		        (:instance bitn-plus-bits (n (expo x)) (m 0))
			(:instance bits-bounds (i (1- (expo x))) (j 0))))))

(defthmd bitn>expo
  (implies (and (not (zp x)) (natp n) (>= n (1+ (expo x))))
           (equal (bitn x n) 0))
  :hints (("Goal" :in-theory (enable bvecp):nonlinearp t
                  :use (expo-upper-bound))))

(local-defthm w0p>=4
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (>= (w0p) 4))
  :rule-classes ()
  :hints (("Goal" :use (expo-fwp-bound (:instance expo-lower-bound (x (fwp))))
                  :in-theory (enable fwp))))


(local-defthm expo-w0-1
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (and (= (bitn (w0) (expo (w0p))) 1)
	        (>= (expo (w0p)) 2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bitn-expo) (expo-s0p-4))
                  :use (w0p>=4  (:instance bitn-w0-w0p (k (expo (w0p)))) (:instance expo>= (x (w0p)) (n 2))))))

(local-defthm w0-bound
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (>= (w0) 4))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp)
                  :use (expo-w0-1 (:instance bitn-plus-bits (x (w0)) (n (expo (w0p))) (m 0))))))

(local-defthm expo-w0-2
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (>= (w0) (expt 2 (expo (w0p)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp):nonlinearp t
                  :use (expo-w0-1
		        (:instance bitn-plus-bits (x (w0)) (n (expo (w0p))) (m 0))))))

(local-defthm expo-w0-3
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (>= (expo (w0)) (expo (w0p))))
  :rule-classes ()
  :hints (("Goal" :use (expo-w0-2
		        (:instance expo>= (x (w0)) (n (expo (w0p))))))))

(local-defthmd expo-w0-4
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (expo (w0)) (expo (w0p))))
  :hints (("Goal" :use (expo-w0-1 expo-w0-3
                        (:instance bitn>expo (x (w0p)) (n (expo (w0))))
                        (:instance bitn-expo (x (w0))))
		  :in-theory (enable bitn-w0-w0p))))

(local-defthm expo-w0-5
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (expo (w0))
                  (1+ (expo (bits (ash (w0) (- 1)) 127 0)))))
  :hints (("Goal" :nonlinearp t
                  :use (w0-bound (:instance bits-bounds (x (LOGNOT (LOGXOR (P) (* 2 (K))))) (i 127) (j 0)))
                  :in-theory (enable w0 bvecp))))

(local-defthmd expo-fw-fwp
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (expo (fw)) (expo (fwp))))
  :hints (("Goal" :use (w0p>=4 expo-w0-4) :in-theory (enable fw fwp))))

(local-defthmd expo-fw
  (equal (expo (fw)) (- 127 (lza)))
  :hints (("Goal" :in-theory (enable fw computelza-lemma lza128-lemma clz-expo))))

(local-defthmd expo-fw-bound
   (<= (expo (fw)) 126)
  :hints (("Goal" :in-theory (enable fw w0)
                  :use ((:instance bits-bounds (x (w0)) (i 127) (j 0))
		        (:instance expo<= (x (fw)) (n 126))))))

(local-defthmd expo-fw-bounds
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (and (<= (expo (fw)) 127) (>= (expo (fw)) 0)))
  :hints (("Goal" :in-theory (enable fw)
                  :use ((:instance bits-bounds (x (ash (w0) (- 1))) (i 127) (j 0))
		        (:instance expo>= (x (fw)) (n 0))
		        (:instance expo<= (x (fw)) (n 127))))))

(defthm lza-bounds
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (and (>= (lza) 1) (<= (lza) 127)))
  :rule-classes ()
  :hints (("Goal" :use (expo-fw expo-fw-bound expo-fw-bounds))))

(defthm natp-lzcnt
  (natp (lzcnt x w))
  :rule-classes (:type-prescription :rewrite))

(defthm natp-lza
  (natp (lza))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :cases ((= (fw) 0)) :in-theory (enable lza128-lemma computelza-lemma fw clz-lzcnt bvecp))))

(defthm lza-pos
  (not (zp (lza)))
  :rule-classes ()
  :hints (("Goal" :use (expo-fw expo-fw-bound))))

(local-defthm integerp-lzap
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (integerp (lzap)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable lzap128-lemma fwp clz-expo bvecp))))

(defthmd lza=lzap
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (equal (lza) (lzap)))
  :hints (("Goal" :use (expo-fwp-lzap expo-fw-fwp expo-fw))))

(defthm lzap-pos
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (not (zp (lzap))))
  :rule-classes ()
  :hints (("Goal" :use (lza=lzap lza-pos))))

(defthm expo-sum-lza
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (or (= (expo (sum)) (- 106 (lza)))
               (= (expo (sum)) (- 107 (lza)))))
  :rule-classes ()
  :hints (("Goal" :use (expo-sum-lzap lza=lzap))))
