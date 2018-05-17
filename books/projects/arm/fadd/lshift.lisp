(in-package "RTL")

(include-book "lza")

(local-defthmd bvecp-expl
  (bvecp (expl) 12)
  :hints (("Goal" :use (bvecp-expa bvecp-expb) :in-theory (enable expl bvecp))))

(defthmd lshift-rewrite
  (implies (= (mulovfl) 0)
           (equal (lshift)
                  (if (= (far) 1)
                      0
                    (if (< (lza) (expl))
                        (lza)
                      (if (= (expl) 0)
                          0
                        (1- (expl)))))))
  :hints (("Goal" :in-theory (enable far-rewrite bvecp expl exps computelshift-lemma lshift*)
           :use (bvecp-expa bvecp-expb lza-bounds))))

(local-defthmd near-exps-0-lshift-rewrite
  (implies (and (= (mulovfl) 0) (or (= (far) 1) (not (> (exps) 0))))
           (equal (lshift) 0))
  :hints (("Goal" :in-theory (enable far-rewrite bvecp expl exps computelshift-lemma lshift*)
           :use (bvecp-expa bvecp-expb lza-bounds))))

(local-defthm natp-lshift
  (implies (= (mulovfl) 0)
           (natp (lshift)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable near-exps-0-lshift-rewrite lshift-rewrite) :use (lza-bounds))))

(local-defthmd bvecp-sum
  (bvecp (sum) 108)
  :hints (("Goal" :in-theory (enable add-lemma sum*))))

(local-defthmd expo-ash-sum
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (<= (expo (ash (sum) (lshift))) 107))
  :hints (("Goal" :use (expo-sum-lza bvecp-expl bvecp-sum lza-bounds
                        (:instance expo-shift (x (sum)) (n (lshift))))
                  :in-theory (enable lshift-rewrite bvecp))))

(local-defthmd bvecp-ash-sum
  (implies (and (= (mulovfl) 0) (= (far) 0) (> (exps) 0))
           (bvecp (ash (sum) (lshift))  108))
  :hints (("Goal" :use (expo-ash-sum bvecp-sum
                        (:instance expo-upper-bound (x (ash (sum) (lshift)))))
                  :nonlinearp t
                  :in-theory (enable bvecp))))

(defthmd sumshft-rewrite
  (implies (= (mulovfl) 0)
           (equal (sumshft) (* (expt 2 (lshift)) (sum))))
  :hints (("Goal" :use (bvecp-ash-sum near-exps-0-lshift-rewrite bvecp-sum)
           :in-theory (enable sumshft))))

(defthmd expshft-rewrite
  (implies (= (mulovfl) 0)
           (equal (expshft)
                  (if (= (far) 1)
                      (if (= (usa) 1)
                          (1- (expl))
                        (expl))
                    (if (< (lza) (expl))
                        (- (expl) (lza))
                      0))))
  :hints (("Goal" :in-theory (enable far-rewrite bvecp expl exps computelshift-lemma expshft*)
           :use (bvecp-expa bvecp-expb lza-bounds))))

(local-defthmd expshft>0-1
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)))
           (> (expl) 0))
  :hints (("Goal" :in-theory (enable far-rewrite bvecp expl exps computelshift-lemma expshft*)
           :use (bvecp-expa bvecp-expb lza-bounds))))

(local-defthmd expshft>0-2
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)))
           (>= (sigl) (expt 2 106)))
  :hints (("Goal" :in-theory (enable opbgeopa cat expl sigl siga sigb)
           :use (expshft>0-1))))

(local-defthmd expshft>0-3
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (usa) 0))
           (>= (sumshft) (expt 2 106)))
  :hints (("Goal" :in-theory (enable lshift-rewrite sumshft-rewrite far-rewrite sum-rewrite)
           :use (expshft>0-2))))

(local-defthmd expshft>0-4
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 1) (= (usa) 1))
           (>= (sigl) (expt 2 107)))
  :hints (("Goal" :in-theory (enable opbgeopa cat expl sigl siga sigb)
           :use (expshft>0-1))))

(local-defthmd expshft>0-5
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 1) (= (usa) 1) (> (exps) 0))
           (>= (expdiff) 2))
  :hints (("Goal" :in-theory (enable far-rewrite expl exps expdiff-rewrite opbgeopa))))

(local-defthmd expshft>0-6
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 1) (= (usa) 1) (> (exps) 0))
           (< (sigshft) (expt 2 106)))
  :hints (("Goal" :in-theory (enable sigshft-rewrite sigs bvecp)
                  :use (bvecp-siga bvecp-sigb expshft>0-5)
		  :nonlinearp t)))

(local-defthmd expshft>0-7
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 1) (= (usa) 1) (= (exps) 0))
           (>= (expdiff) 1))
  :hints (("Goal" :in-theory (enable far-rewrite expl exps expdiff-rewrite opbgeopa))))

(local-defthmd expshft>0-8
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 1) (= (usa) 1) (= (exps) 0))
           (< (sigs) (expt 2 107)))
  :hints (("Goal" :use (bvecp-siga-0 bvecp-sigb-0)
                  :in-theory (enable bvecp exps opbgeopa sigs))))

(local-defthmd expshft>0-9
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 1) (= (usa) 1) (= (exps) 0))
           (< (sigshft) (expt 2 106)))
  :hints (("Goal" :in-theory (enable sigshft-rewrite)
                  :use (expshft>0-7 expshft>0-8)
		  :nonlinearp t)))

(local-defthmd expshft>0-10
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 1) (= (usa) 1))
           (>= (sumshft) (expt 2 106)))
  :hints (("Goal" :use (expshft>0-9 expshft>0-6 expshft>0-4)
                  :in-theory (enable sum-rewrite sumshft-rewrite lshift-rewrite))))

(local-defthmd expshft>0-11
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 0))
           (and (= (lshift) (lza))
	        (< (lza) (expl))))
  :hints (("Goal" :use (expshft>0-9 expshft>0-6 expshft>0-4)
                  :in-theory (enable sum-rewrite sumshft-rewrite expshft-rewrite lshift-rewrite))))

(local-defthmd expshft>0-12
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 0))
           (> (expl) 1))
  :hints (("Goal" :use (expshft>0-11 lza-pos))))

(local-defthmd expshft>0-13
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 0))
           (> (exps) 0))
  :hints (("Goal" :use (expshft>0-12)
                  :in-theory (enable far-rewrite opbgeopa expl exps))))

(local-defthmd expshft>0-14
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (far) 0))
           (>= (expo (sumshft)) 106))
  :hints (("Goal" :use (expshft>0-13 expshft>0-11 expo-sum-lza expo-sum-lzap-7
                        (:instance expo-shift (x (sum)) (n (lshift))))
                  :in-theory (enable sumshft-rewrite))))

(defthmd expshft>0-sumshft
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)))
           (>= (expo (sumshft)) 106))
  :hints (("Goal" :use (expshft>0-14 expshft>0-10 expshft>0-3
                        (:instance expo>= (x (sumshft)) (n 106))))))

(local-defthmd expshft=0-1
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 1))
           (and (= (usa) 0) (= (expl) 0)))
  :hints (("Goal" :in-theory (enable expshft-rewrite expl exps far-rewrite opbgeopa)
                  :use (bvecp-expa bvecp-expb))))

(local-defthmd expshft=0-2
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 1))
           (and (< (sigl) (expt 2 106))
	        (< (sigs) (expt 2 106))))
  :hints (("Goal" :in-theory (enable siga sigb sigl sigs expl exps cat)
                  :use (expshft=0-1 bvecp-expa bvecp-expb
		        (:instance bits-bounds (x (fraca)) (i 104) (j 0))
		        (:instance bits-bounds (x (fracb)) (i 104) (j 0))))))

(local-defthmd expshft=0-3
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 1))
           (< (sumshft) (expt 2 107)))
  :hints (("Goal" :in-theory (enable sum-rewrite lshift-rewrite sumshft-rewrite sigshft-rewrite expdiff-rewrite expl)
                  :use (bvecp-expa bvecp-expb expshft=0-1 expshft=0-2))))

(local-defthmd expshft=0-4
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 0))
           (>= (lza) (expl)))
  :hints (("Goal" :in-theory (enable expshft-rewrite expl exps far-rewrite opbgeopa)
                  :use (bvecp-expa bvecp-expb))))

(local-defthm expshft=0-5
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 0) (<= (expl) 1))
           (equal (lshift) 0))
  :hints (("Goal" :in-theory (enable lshift-rewrite)
                  :use (expshft=0-4))))

(local-defthmd expshft=0-6
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 0) (<= (expl) 1))
           (<= (sumshft) (sigl)))
  :hints (("Goal" :in-theory (enable far-rewrite sum-rewrite sumshft-rewrite))))

(local-defthmd expshft=0-7
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 0) (<= (expl) 1))
           (< (sumshft) (expt 2 107)))
  :hints (("Goal" :in-theory (enable sigl siga sigb cat)
                  :use (expshft=0-6
		        (:instance bits-bounds (x (fraca)) (i 104) (j 0))
		        (:instance bits-bounds (x (fracb)) (i 104) (j 0))))))

(local-defthmd expshft=0-8
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 0) (> (expl) 1))
           (> (exps) 0))
  :hints (("Goal" :in-theory (enable expl exps far-rewrite opbgeopa))))

(local-defthmd expshft=0-9
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 0) (> (expl) 1))
           (<= (lshift) (1- (lza))))
  :hints (("Goal" :in-theory (enable lshift-rewrite)
                  :use (expshft=0-4))))

(local-defthmd expshft=0-10
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 0) (> (expl) 1))
           (<= (expo (sumshft)) 106))
  :hints (("Goal" :in-theory (enable sumshft-rewrite)
                  :use (expshft=0-9 expshft=0-8 expo-sum-lza
		        (:instance expo-shift (x (sum)) (n (lshift)))))))

(local-defthmd expshft=0-11
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (far) 0) (> (expl) 1))
           (< (sumshft) (expt 2 107)))
  :hints (("Goal" :nonlinearp t :use (expshft=0-10 (:instance expo-upper-bound (x (sumshft)))))))

(defthmd expshft=0-sumshft
  (implies (and (= (mulovfl) 0) (= (expshft) 0))
           (<= (expo (sumshft)) 106))
  :hints (("Goal" :use (expshft=0-11 expshft=0-7 expshft=0-3
                        (:instance expo<= (x (sumshft)) (n 106))))))

(local-defthm expshft-sumshft-1
  (implies (and (= (mulovfl) 0) (= (far) 1) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (<=  (absval (expshft) (sumshft)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (expshft) (1+ (sumshft))))
		(iff (= (absval (expshft) (sumshft)) (abs (+ (a) (b))))
                     (= (stk) 0))))
  :rule-classes ()
  :hints (("Goal" :use (sum-bounds-0) :in-theory (enable explp sumshft-rewrite lshift-rewrite expshft-rewrite))))

(local-defthm expshft-sumshft-2
  (implies (and (= (mulovfl) 0) (= (far) 0))
           (or (= (expdiff) 0) (= (expdiff) 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable opbgeopa expdiff-rewrite far-rewrite))))

(local-defthm expshft-sumshft-3
  (implies (and (= (mulovfl) 0) (= (far) 0) (= (stk) 1))
           (equal (sigshft) (* (expt 2 (- (expdiff))) (sigs))))
  :hints (("Goal" :in-theory (enable sigs siga sigb cat sigshft-rewrite)
                  :use (expshft-sumshft-2))))

(local-defthm expshft-sumshft-4
  (implies (and (= (mulovfl) 0) (= (far) 0) (= (stk) 1))
           (equal (shiftout) 0))
  :hints (("Goal" :in-theory (enable shiftout-rewrite))))

(local-defthm expshft-sumshft-5
  (implies (and (= (mulovfl) 0) (= (far) 0) (= (stk) 1))
           (equal (mulstk) 1))
  :hints (("Goal" :in-theory (enable stk* add-lemma) :use (near-shiftout-0))))

(local-defthmd expshft-sumshft-6
  (implies (and (= (mulovfl) 0) (= (far) 0) (= (stk) 1))
           (equal (expb) 0))
  :hints (("Goal" :use (expb-pos-mulstk expb-pos-b))))

(local-defthm expshft-sumshft-7
  (implies (and (= (mulovfl) 0) (= (far) 0) (= (stk) 1))
           (or (= (expl) 0) (= (expl) 1)))
  :rule-classes ()
  :hints (("Goal" :use (expshft-sumshft-6 bvecp-expa) :in-theory (enable expl far-rewrite opbgeopa))))

(local-defthmd expshft-sumshft-8
  (implies (and (= (mulovfl) 0) (= (far) 0) (< (lza) (expl)))
           (equal (sumshft) (* (expt 2 (lza)) (sum))))
  :hints (("Goal" :in-theory (enable sumshft-rewrite lshift-rewrite expshft-rewrite))))

(local-defthmd expshft-sumshft-9
  (implies (and (= (mulovfl) 0) (= (far) 0) (< (lza) (expl)))
           (equal (absval (expl) (sum)) (absval (expshft) (sumshft))))
  :hints (("Goal" :in-theory (enable absval expshft-sumshft-8 expshft-rewrite))))

(local-defthmd expshft-sumshft-10
  (implies (and (= (mulovfl) 0) (= (far) 0) (< (lza) (expl)) (= (stk) 1))
           (and (equal (sumshft) (sum))
	        (equal (expshft) (expl))))
  :hints (("Goal" :in-theory (enable expshft-rewrite sumshft-rewrite lshift-rewrite)
                  :use (expshft-sumshft-7))))

(local-defthmd expshft-sumshft-11
  (implies (and (= (mulovfl) 0) (= (far) 0))
           (equal (explp) (expl)))
  :hints (("Goal" :in-theory (enable explp far-rewrite))))

(defthm stk-0-1
  (member (stk) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable add-lemma stk*))))

(local-defthm expshft-sumshft-16
  (< (absval (expshft) (sumshft)) (absval (expshft) (1+ (sumshft))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable absval) :nonlinearp t)))

(local-defthm expshft-sumshft-13
  (implies (and (= (mulovfl) 0) (= (far) 0) (< (lza) (expl)) (or (> (expb) 0)
                (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (<=  (absval (expshft) (sumshft)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (expshft) (1+ (sumshft))))
		(iff (= (absval (expshft) (sumshft)) (abs (+ (a) (b))))
                     (= (stk) 0))))
  :rule-classes ()
  :hints (("Goal" :use (expshft-sumshft-11 stk-0-1 expshft-sumshft-1 expshft-sumshft-9
                        expshft-sumshft-16 expshft-sumshft-10 sum-bounds-0)
		  :in-theory (disable abs))))

(local-defthmd expshft-sumshft-14
  (implies (and (= (mulovfl) 0) (= (far) 0) (>= (lza) (expl)))
           (equal (expshft) 0))
  :hints (("Goal" :in-theory (enable expshft-rewrite sumshft-rewrite lshift-rewrite))))

(local-defthmd expshft-sumshft-15
  (implies (and (= (mulovfl) 0) (= (far) 0) (>= (lza) (expl)) (= (expl) 0))
           (and (equal (expshft) (expl))
	        (equal (sumshft) (sum))))
  :hints (("Goal" :in-theory (enable expshft-sumshft-14 expshft-rewrite sumshft-rewrite lshift-rewrite))))

(local-defthmd expshft-sumshft-17
  (implies (and (= (mulovfl) 0) (= (far) 0) (>= (lza) (expl)) (> (expl) 0))
           (equal (absval (expl) (sum)) (absval (expshft) (sumshft))))
  :hints (("Goal" :in-theory (enable lshift-rewrite sumshft-rewrite absval))))

(local-defthmd expshft-sumshft-18
  (implies (and (= (mulovfl) 0) (= (far) 0) (>= (lza) (expl)) (> (expl) 0) (= (stk) 1))
           (equal (absval (expl) (1+ (sum))) (absval (expshft) (1+ (sumshft)))))
  :hints (("Goal" :use (expshft-sumshft-7) :in-theory (enable lshift-rewrite sumshft-rewrite absval))))

(local-defthm expshft-sumshft-19
              (implies (and (= (mulovfl) 0) (= (far) 0) (>= (lza) (expl))
                            (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (<=  (absval (expshft) (sumshft)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (expshft) (1+ (sumshft))))
		(iff (= (absval (expshft) (sumshft)) (abs (+ (a) (b))))
                     (= (stk) 0))))
  :rule-classes ()
  :hints (("Goal" :use (expshft-sumshft-11 stk-0-1 expshft-sumshft-16 expshft-sumshft-15
                        expshft-sumshft-17 expshft-sumshft-18 sum-bounds-0)
		  :in-theory (disable abs))))

(defthm expshft-sumshft-0
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (<=  (absval (expshft) (sumshft)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (expshft) (1+ (sumshft))))
		(iff (= (absval (expshft) (sumshft)) (abs (+ (a) (b))))
                     (= (stk) 0))))
  :rule-classes ()
  :hints (("Goal" :use (expshft-sumshft-1 expshft-sumshft-13 expshft-sumshft-19))))

(defthm rat-abs
  (implies (rationalp x) (rationalp (abs x)))
  :rule-classes (:type-prescription :rewrite))

(defthm int-expshft
   (implies (= (mulovfl) 0)
            (integerp (expshft)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable expshft-rewrite))))

(local-defthm expshft-sumshft-20
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (<= (absval (expshft) (chop (sumshft) -53))
	       (absval (expshft) (sumshft))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (chop absval) (abs)) :nonlinearp t)))

(local-defthm expshft-sumshft-21
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (<= (absval (expshft) (1+ (sumshft)))
	       (absval (expshft) (+ (chop (sumshft) -53) (expt 2 53)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (chop absval) (abs)) :nonlinearp t)))

(local-defthm expshft-sumshft-22
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (iff (= (absval (expshft) (chop (sumshft) -53)) (abs (+ (a) (b))))
                (and (= (stk) 0)
		     (= (sumshft) (chop (sumshft) -53)))))
  :rule-classes ()
  :hints (("Goal" :use (expshft-sumshft-0) :in-theory (e/d (chop absval) (abs)) :nonlinearp t)))

(local-defthm expshft-sumshft-23
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (iff (= (sumshft) (chop (sumshft) -53))
	        (= (bits (sumshft) 52 0) 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-def (x (sumshft)) (y (expt 2 53))))
                  :in-theory (enable bits chop))))

(local-defthm expshft-sumshft-24
  (implies (and (= (mulovfl) 0) (or (> (expb) 0) (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (<=  (absval (expshft) (chop (sumshft) -53)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (expshft) (+ (chop (sumshft) -53) (expt 2 53))))
		(iff (= (absval (expshft) (chop (sumshft) -53)) (abs (+ (a) (b))))
                     (and (= (bits (sumshft) 52 0) 0)
		          (= (stk) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
                  :use (expshft-sumshft-0 expshft-sumshft-20 expshft-sumshft-21 expshft-sumshft-22
		        expshft-sumshft-23))))

(local-defthm expshft-sumshft-25
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (equal (sumshft) (sum)))
  :hints (("Goal" :in-theory (enable far-rewrite opbgeopa lshift-rewrite expl-rewrite sumshft-rewrite))))

(local-defthm expshft-sumshft-26
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))) (= (far) 1))
           (equal (expshft) (explp)))
  :hints (("Goal" :in-theory (enable explp far-rewrite opbgeopa lshift-rewrite expl-rewrite expshft-rewrite))))

(local-defthmd expshft-sumshft-27
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))) (= (far) 0))
           (and (member (expshft) '(0 1))
	        (member (explp) '(0 1))))
  :hints (("Goal" :use (lza-bounds)
                  :in-theory (enable exps explp far-rewrite opbgeopa lshift-rewrite expl-rewrite expshft-rewrite))))

(local-defthm expshft-sumshft-28
  (equal (absval 1 x) (absval 0 x))
  :hints (("Goal" :in-theory (enable absval))))

(local-defthm expshft-sumshft-29
  (implies (and (= (mulovfl) 0) (= (expb) 0) (not (and (= (bits (sigb) 52 0) 0) (= (mulstk) 0))))
           (and (<=  (absval (expshft) (chop (sumshft) -53)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (expshft) (+ (chop (sumshft) -53) (expt 2 53))))
		(iff (= (absval (expshft) (chop (sumshft) -53)) (abs (+ (a) (b))))
                     (and (= (bits (sumshft) 52 0) 0)
		          (= (stk) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (stk* add-lemma) (abs))
                  :use (sum-bounds-1 expshft-sumshft-27))))

(defthm expshft-sumshft
  (implies (= (mulovfl) 0)
           (and (<=  (absval (expshft) (chop (sumshft) -53)) (abs (+ (a) (b))))
	        (< (abs (+ (a) (b))) (absval (expshft) (+ (chop (sumshft) -53) (expt 2 53))))
		(iff (= (absval (expshft) (chop (sumshft) -53)) (abs (+ (a) (b))))
                     (and (= (bits (sumshft) 52 0) 0)
		          (= (stk) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (stk* add-lemma) (abs))
                  :use (expshft-sumshft-29 expshft-sumshft-24))))
