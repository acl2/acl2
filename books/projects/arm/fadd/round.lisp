(in-package "RTL")

(include-book "lshift")

(local-defthm natp-lshift
  (implies (= (mulovfl) 0)
           (natp (lshift)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable lshift-rewrite))))

(defthmd lovfl-rewrite
  (implies (= (mulovfl) 0)
           (equal (lovfl) (bitn (sumshft) 55)))
  :hints (("Goal" :in-theory (enable bvecp sumshft-rewrite lovfl lovflmask)
                  :nonlinearp t :cases ((<= (lshift) 55))
                  :use ((:instance fl-unique (x (expt 2 (- 55 (lshift)))) (n 0))
		        (:instance logand-bit (x (sum)) (n (- 55 (lshift))))
                        (:instance bitn-shift-up (x (sum)) (n (- 55 (lshift))) (k (lshift)))))))

(defthmd govfl-rewrite
  (implies (= (mulovfl) 0)
           (equal (govfl) (bitn (sumshft) 54)))
  :hints (("Goal" :in-theory (enable bvecp sumshft-rewrite govfl govflmask lovflmask)
                  :nonlinearp t :cases ((<= (lshift) 54))
                  :use ((:instance fl-unique (x (expt 2 (- 54 (lshift)))) (n 0))
		        (:instance logand-bit (x (sum)) (n (- 54 (lshift))))
                        (:instance bitn-shift-up (x (sum)) (n (- 54 (lshift))) (k (lshift)))))))

(defthmd lnorm-rewrite
  (implies (= (mulovfl) 0)
           (equal (lnorm) (bitn (sumshft) 54)))
  :hints (("Goal" :in-theory (enable bvecp sumshft-rewrite lnorm lovflmask lnormmask)
                  :nonlinearp t :cases ((<= (lshift) 54))
                  :use ((:instance fl-unique (x (expt 2 (- 54 (lshift)))) (n 0))
		        (:instance logand-bit (x (sum)) (n (- 54 (lshift))))
                        (:instance bitn-shift-up (x (sum)) (n (- 54 (lshift))) (k (lshift)))))))

(defthmd gnorm-rewrite
  (implies (= (mulovfl) 0)
           (equal (gnorm) (bitn (sumshft) 53)))
  :hints (("Goal" :in-theory (enable bvecp sumshft-rewrite gnorm lovflmask gnormmask)
                  :nonlinearp t :cases ((<= (lshift) 53))
                  :use ((:instance fl-unique (x (expt 2 (- 53 (lshift)))) (n 0))
		        (:instance logand-bit (x (sum)) (n (- 53 (lshift))))
                        (:instance bitn-shift-up (x (sum)) (n (- 53 (lshift))) (k (lshift)))))))

(defthmd sovfl-lemma
  (implies (= (mulovfl) 0)
           (iff (equal (sovfl) 0)
	        (and (equal (bits (sumshft) 53 0) 0)
                     (equal (stk) 0))))
  :hints (("Goal" :in-theory (enable bvecp sumshft-rewrite sovfl sovflmask)
                  :nonlinearp t
                  :use (stk-0-1
		        (:instance fl-unique (x (/ (1- (expt 2 54)) (expt 2 (lshift)))) (n (1- (expt 2 (- 54 (lshift))))))
		        (:instance fl-unique (x (/ (1- (expt 2 54)) (expt 2 (lshift)))) (n 0))
		        (:instance logand-bits (x (sum)) (n (- 54 (lshift))) (k 0))
                        (:instance bits-shift-up-2 (x (sum)) (i (- 53 (lshift))) (k (lshift)))))))

(defthmd sovfl-rewrite
  (implies (= (mulovfl) 0)
           (equal (sovfl)
	          (if (and (equal (bits (sumshft) 53 0) 0)
                           (equal (stk) 0))
		      0 1)))
  :hints (("Goal" :in-theory (enable sovfl) :use (sovfl-lemma))))

(local-defthm snormmask-rewrite
  (implies (= (mulovfl) 0)
           (equal (snormmask) (fl (/ (1- (expt 2 53)) (expt 2 (lshift))))))
  :hints (("Goal" :in-theory (e/d (bvecp snormmask sovflmask) (fl/int-rewrite fl/int-rewrite-alt))
                  :nonlinearp t
                  :use ((:instance fl/int-rewrite (x (/ (1- (expt 2 54)) (expt 2 (lshift)))) (n 2))
		        (:instance fl/int-rewrite (x (/ (1- (expt 2 54)) 2)) (n (expt 2 (lshift))))))))

(local-defthmd snorm-lemma
  (implies (= (mulovfl) 0)
           (iff (equal (snorm) 0)
	        (and (equal (bits (sumshft) 52 0) 0)
                     (equal (stk) 0))))
  :hints (("Goal" :in-theory (e/d (bvecp sumshft-rewrite snorm sovflmask) (snormmask fl-def))
                  :nonlinearp t :cases ((<= (lshift) 53))
                  :use (stk-0-1
		        (:instance fl-unique (x (/ (1- (expt 2 53)) (expt 2 (lshift)))) (n (1- (expt 2 (- 53 (lshift))))))
		        (:instance fl-unique (x (/ (1- (expt 2 53)) (expt 2 (lshift)))) (n 0))
		        (:instance logand-bits (x (sum)) (n (- 53 (lshift))) (k 0))
                        (:instance bits-shift-up-2 (x (sum)) (i (- 52 (lshift))) (k (lshift)))))))

(defthmd snorm-rewrite
  (implies (= (mulovfl) 0)
           (equal (snorm)
	          (if (and (equal (bits (sumshft) 52 0) 0)
                           (equal (stk) 0))
		      0 1)))
  :hints (("Goal" :in-theory (enable snorm) :use (snorm-lemma))))

(defthm gsnorm-0-1
  (and (member (gnorm) '(0 1))
       (member (snorm) '(0 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable gnorm-rewrite snorm-rewrite))))

(defthm gsovfl-0-1
  (and (member (govfl) '(0 1))
       (member (sovfl) '(0 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable govfl-rewrite sovfl-rewrite))))

(defund mode () (fpscr-rc (rin)))

(defund modep () (if1 (signout) (flip-mode (mode)) (mode)))

(in-theory (disable (mode) (modep)))

(local-defthmd signa-sign
  (implies (not (= (a) 0))
           (equal (signa) (if (< (a) 0) 1 0)))
  :hints (("Goal" :in-theory (enable absval val a) :use (signa-0-1))))

(defthmd signl-rewrite
  (implies (= (mulovfl) 0)
           (equal (signl)
                  (if (> (+ (a) (b)) 0) 0 1)))
  :hints (("Goal" :in-theory (enable absval val signa-sign opbgeopa-b>=a signl* add-lemma)
		  :use (signa-sign signa-0-1 signb-0-1 expb-0-b expb-pos-b a+b<>0))))

(defthmd rnd-modep-rmode
  (implies (= (mulovfl) 0)
           (equal (rnd (+ (a) (b)) (mode) 53)
                  (if (= (signl) 0)
	              (rnd (abs (+ (a) (b))) (modep) 53)
    	            (- (rnd (abs (+ (a) (b))) (modep) 53)))))
  :hints (("Goal" :in-theory (enable modep signout signl-rewrite)
                  :use ((:instance rnd-minus (x (abs (+ (a) (b)))) (mode (mode)) (n 53))))))

(defthmd drnd-modep-rmode
  (implies (= (mulovfl) 0)
           (equal (drnd (+ (a) (b)) (mode) (dp))
                  (if (= (signl) 0)
	              (drnd (abs (+ (a) (b))) (modep) (dp))
	            (- (drnd (abs (+ (a) (b))) (modep) (dp))))))
  :hints (("Goal" :in-theory (enable modep signout signl-rewrite)
                  :use ((:instance drnd-minus (x (abs (+ (a) (b)))) (mode (mode)) (f (dp)))))))

(defthmd expo-sumshft
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)))
           (equal (expo (sumshft))
	          (if1 (bitn (sumshft) 107) 107 106)))
  :hints (("Goal" :in-theory (enable sumshft)
                  :use (expshft>0-sumshft
		        (:instance bits-bounds (x (* (sum) (expt 2 (lshift)))) (i 107) (j 0))
			(:instance expo<= (x (bits (* (sum) (expt 2 (lshift))) 107 0)) (n 107))
		        (:instance bitn>expo (x (sumshft)) (n 107))
			(:instance bitn-expo (x (sumshft)))))))


(defthm rationalp-a
  (rationalp (a))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable a val absval))))

(defthm rationalp-abs
  (rationalp (abs (+ (a) (b))))
  :rule-classes (:type-prescription))

(defthm modep-common
  (common-mode-p (modep))
  :hints (("Goal" :in-theory (enable common-mode-p ieee-rounding-mode-p flip-mode modep mode fpscr-rc)
                  :use ((:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defund z1 ()
  (* (expt 2 (- (+ 53 (1- (expt 2 10))) (expshft)))
     (abs (+ (a) (b)))))

(local-defund x1 () (fl (* (expt 2 -53) (sumshft))))

(local-defun e1 () (expo (x1)))

(local-in-theory (disable (z1) (x1) (e1)))

(local-defthm rationalp-z1
  (implies (= (mulovfl) 0)
           (rationalp (z1)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable expshft-rewrite z1))))

(defthmd expo-fl
  (implies (and (rationalp x) (>= x 1))
           (equal (expo (fl x))
                  (expo x)))
  :hints (("Goal" :use (expo-lower-bound expo-upper-bound
                        (:instance expo>= (n 0))
                        (:instance expo-unique (x (fl x)) (n (expo x)))))))

(local-defthmd expo-x1
  (implies (and (= (mulovfl) 0) (>= (expo (sumshft)) 53))
           (equal (expo (x1)) (- (expo (sumshft)) 53)))
  :hints (("Goal" :in-theory (enable x1 expo-fl)
                  :use ((:instance expo-shift (x (sumshft)) (n -53))
                        (:instance expo-lower-bound (x (* (expt 2 -53) (sumshft))))))))

(local-defthm rnd-expshft-pos-1
  (and (iff (<= (* (x1) (expt 2 (+ -1076 (expshft))))
                (abs (+ (a) (b))))
            (<= (x1) (z1)))
       (iff (< (* (x1) (expt 2 (+ -1076 (expshft))))
                (abs (+ (a) (b))))
            (< (x1) (z1))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable z1) :nonlinearp t)))

(local-defthm rnd-expshft-pos-2
  (iff (< (abs (+ (a) (b)))
          (+ (expt 2 (+ -1076 (expshft)))
             (* (x1) (expt 2 (+ -1076 (expshft))))))
       (< (z1) (+ 1 (x1))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable z1) :nonlinearp t)))

(defthm natp-expshft
  (implies (= (mulovfl) 0)
           (natp (expshft)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (bvecp-expa bvecp-expb) :in-theory (enable expshft-rewrite expl far-rewrite))))

(local-defthm rnd-expshft-pos-3
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)))
           (and (>= (z1) (x1))
	        (< (z1) (1+ (x1)))
		(iff (= (z1) (x1)) (and (= (bits (sumshft) 52 0) 0) (= (stk) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (absval x1 chop) (abs))
                  :use (rnd-expshft-pos-1 rnd-expshft-pos-2 expshft-sumshft))))

(local-defthm rnd-expshft-pos-4
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)))
           (and (= (fl (z1)) (x1))
	        (iff (integerp (z1)) (and (= (bits (sumshft) 52 0) 0) (= (stk) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (z1 absval) (abs))
                  :use (rnd-expshft-pos-3))))

(local-defthmd rnd-5
  (implies (= (mulovfl) 0)
           (equal (rtz (x1) 53)
	          (* (expt 2 (- (e1) 52))
		     (bits (x1) (e1) (- (e1) 52)))))
  :hints (("Goal" :in-theory (enable x1) :use ((:instance bits-rtz (x (x1)) (n (1+ (e1))) (k 53))))))

(local-defthmd rnd-6
  (implies (= (mulovfl) 0)
           (equal (fp+ (rtz (x1) 53) 53)
	          (* (expt 2 (- (e1) 52))
		     (1+ (bits (x1) (e1) (- (e1) 52))))))
  :hints (("Goal" :in-theory (e/d (x1 rnd-5 fp+) (x1 expo-rtz))
                  :use ((:instance expo-rtz (x (x1)) (n 53))))))

(local-defthmd rnd-expshft-pos-7
  (implies (and (= (mulovfl) 0) (>= (expo (sumshft)) 106))
           (>= (abs (+ (a) (b))) (spn (dp))))
  :hints (("Goal" :in-theory (enable x1 absval chop spn dp)
                  :nonlinearp t
                  :use (expshft-sumshft expo-sumshft expo-x1 (:instance expo-lower-bound (x (x1)))))))

(local-defthmd bits-x1
  (implies (and (natp i) (natp j))
           (equal (bits (x1) i j)
                  (bits (sumshft) (+ i 53) (+ j 53))))
  :hints (("Goal" :in-theory (enable x1) :use ((:instance bits-shift-down-1 (x (sumshft)) (k 53))))))

(local-defthmd bitn-x1
  (implies (natp i)
           (equal (bitn (x1) i)
                  (bitn (sumshft) (+ i 53))))
  :hints (("Goal" :use ((:instance bits-x1 (j i))))))

(defun stk1 () (if (and (= (stk) 0) (= (bits (sumshft) 52 0) 0)) 0 1))

(in-theory (disable (stk1)))

(local-defthmd rnd-expshft-pos-8
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (equal (incovfl)
	          (if (roundup-pos (x1) (e1) (stk1) (modep) 53) 1 0)))
  :hints (("Goal" :in-theory (enable fpscr-rc roundup-pos rnddir computernddir modep
                              lovfl-rewrite govfl-rewrite sovfl-rewrite rndinfo-lemma signout
			      bits-x1 bitn-x1 expo-x1 expo-sumshft incovfl* mode rmode flip-mode)
                  :use (stk-0-1
		        (:instance bitn-plus-bits (x (sumshft)) (n 54) (m 0))
		        (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))
		        (:instance bitn-plus-bits (x (sumshft)) (n 54) (m 53))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd rnd-expshft-pos-9
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (equal (rnd (z1) (modep) 53)
	          (if (= (incovfl) 0)
		      (rtz (x1) 53)
		    (fp+ (rtz (x1) 53) 53))))
  :hints (("Goal" :in-theory (enable rnd-expshft-pos-8)
                  :use (expo-x1 stk-0-1 rnd-expshft-pos-3 rnd-expshft-pos-4
		        (:instance roundup-pos-thm (mode (modep)) (z (z1)) (n 53))
		        (:instance expo-lower-bound (x (x1)))))))

(defthm incovfl-0-1
  (member (incovfl) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rndinfo-lemma incovfl*))))

(local-defthmd rnd-expshft-pos-10
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (equal (rnd (z1) (modep) 53)
	          (* 4
		     (+ (bits (sumshft) 107 55) (incovfl)))))
  :hints (("Goal" :in-theory (enable bits-x1 expo-x1 rnd-expshft-pos-9)
                  :use (incovfl-0-1 rnd-5 rnd-6))))

(local-defthmd rnd-expshft-pos-11
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (equal (rnd (z1) (modep) 53)
	          (* 4 (sumovfl))))
  :hints (("Goal" :in-theory (enable rnd-expshft-pos-10 sumunrnd sumovfl bits-bits bvecp)
                  :use (incovfl-0-1 (:instance bits-bounds (x (sumunrnd)) (i 53) (j 1))))))

(local-defthmd rnd-expshft-pos-12
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (equal (rnd (abs (+ (a) (b))) (modep) 53)
	          (* (expt 2 (- (expshft) (+ (1- (expt 2 10)) 51)))
		     (sumovfl))))
  :hints (("Goal" :in-theory (e/d (z1) (abs))
                  :use (rnd-expshft-pos-11
		        (:instance rnd-shift (x (abs (+ (a) (b)))) (mode (modep))
			                     (n 53) (k (- (+ 53 (1- (expt 2 10))) (expshft))))))))

(local-defthmd rnd-expshft-pos-13
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (iff (exactp (z1) 53)
	        (and (= (bits (sumshft) 54 0) 0)
		     (= (stk) 0))))
  :hints (("Goal" :in-theory (enable bits-x1)
                  :use (stk-0-1 rnd-expshft-pos-3 rnd-expshft-pos-4 expo-x1
		        (:instance roundup-pos-thm (mode (modep)) (z (z1)) (n 53))
			(:instance bitn-plus-bits (x (sumshft)) (n 54) (m 53))
			(:instance bitn-plus-bits (x (sumshft)) (n 54) (m 0))
			(:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))
		        (:instance expo-lower-bound (x (x1)))))))

(local-defthmd rnd-expshft-pos-14
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (iff (exactp (z1) 53)
	        (and (= (govfl) 0)
		     (= (sovfl) 0))))
  :hints (("Goal" :in-theory (enable rnd-expshft-pos-13 govfl-rewrite sovfl-rewrite)
                  :use ((:instance bitn-plus-bits (x (sumshft)) (n 54) (m 0))))))

(local-defthmd rnd-expshft-pos-15
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (iff (exactp (abs (+ (a) (b))) 53)
	        (and (= (govfl) 0)
		     (= (sovfl) 0))))
  :hints (("Goal" :in-theory (e/d (z1) (abs))
                  :use (rnd-expshft-pos-14
		        (:instance exactp-shift (x (abs (+ (a) (b))))
			                        (k (- (+ 53 (1- (expt 2 10))) (expshft)))
						(n 53))))))

(defthmd rnd-expshft-pos-107
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 107))
           (and (>= (abs (+ (a) (b))) (spn (dp)))
	        (equal (rnd (abs (+ (a) (b))) (modep) 53)
	               (* (expt 2 (- (expshft) (+ (1- (expt 2 10)) 51)))
		          (sumovfl)))
	        (iff (equal (rnd (abs (+ (a) (b))) (modep) 53)
		            (abs (+ (a) (b))))
	             (and (= (govfl) 0)
		          (= (sovfl) 0)))))
  :hints (("Goal" :use (rnd-expshft-pos-7 rnd-expshft-pos-12 rnd-expshft-pos-15
                        (:instance rnd-exactp-b (x (abs (+ (a) (b)))) (mode (modep)) (n 53))))))

(local-defthmd rnd-expshft-pos-8-b
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (equal (incnorm)
	          (if (roundup-pos (x1) (e1) (stk1) (modep) 53) 1 0)))
  :hints (("Goal" :in-theory (enable fpscr-rc roundup-pos rnddir computernddir modep
                              lnorm-rewrite gnorm-rewrite snorm-rewrite rndinfo-lemma signout
			      bits-x1 bitn-x1 expo-x1 expo-sumshft incnorm* rmode mode flip-mode)
                  :use (stk-0-1
		        (:instance bitn-plus-bits (x (sumshft)) (n 54) (m 0))
		        (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))
		        (:instance bitn-plus-bits (x (sumshft)) (n 54) (m 53))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd rnd-expshft-pos-9-b
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (equal (rnd (z1) (modep) 53)
	          (if (= (incnorm) 0)
		      (rtz (x1) 53)
		    (fp+ (rtz (x1) 53) 53))))
  :hints (("Goal" :in-theory (enable rnd-expshft-pos-8-b)
                  :use (expo-x1 stk-0-1 rnd-expshft-pos-3 rnd-expshft-pos-4
		        (:instance roundup-pos-thm (mode (modep)) (z (z1)) (n 53))
		        (:instance expo-lower-bound (x (x1)))))))

(defthm incnorm-0-1
  (member (incnorm) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rndinfo-lemma incnorm*))))

(local-defthmd rnd-expshft-pos-10-b
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (equal (rnd (z1) (modep) 53)
	          (* 2
		     (+ (bits (sumshft) 107 54) (incnorm)))))
  :hints (("Goal" :in-theory (enable bits-x1 expo-x1 rnd-expshft-pos-9-b)
                  :use (incnorm-0-1 rnd-5 rnd-6
			(:instance bitn-plus-bits (x (sumshft)) (n 107) (m 54))
			(:instance bitn>expo (x (sumshft)) (n 107))))))

(local-defthmd rnd-expshft-pos-11-b
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (equal (rnd (z1) (modep) 53)
	          (* 2 (sumnorm))))
  :hints (("Goal" :in-theory (enable rnd-expshft-pos-10-b sumunrnd sumnorm bits-bits bvecp)
                  :use (incnorm-0-1
		        (:instance bits-bounds (x (sumshft)) (i 106) (j 54))
			(:instance bitn-plus-bits (x (sumshft)) (n 107) (m 54))
			(:instance bitn>expo (x (sumshft)) (n 107))))))
			
(local-defthmd rnd-expshft-pos-12-b
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (equal (rnd (abs (+ (a) (b))) (modep) 53)
	          (* (expt 2 (- (expshft) (+ (1- (expt 2 10)) 52)))
		     (sumnorm))))
  :hints (("Goal" :in-theory (e/d (z1) (abs))
                  :use (rnd-expshft-pos-11-b
		        (:instance rnd-shift (x (abs (+ (a) (b)))) (mode (modep))
			                     (n 53) (k (- (+ 53 (1- (expt 2 10))) (expshft))))))))

(local-defthmd rnd-expshft-pos-13-b
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (iff (exactp (z1) 53)
	        (and (= (bits (sumshft) 53 0) 0)
		     (= (stk) 0))))
  :hints (("Goal" :in-theory (enable bitn-x1 bits-x1)
                  :use (stk-0-1 rnd-expshft-pos-3 rnd-expshft-pos-4 expo-x1
			(:instance bitn-plus-bits (x (sumshft)) (n 54) (m 53))
			(:instance bitn-plus-bits (x (sumshft)) (n 54) (m 0))
			(:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))
		        (:instance roundup-pos-thm (mode (modep)) (z (z1)) (n 53))
		        (:instance expo-lower-bound (x (x1)))))))

(local-defthmd rnd-expshft-pos-14-b
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (iff (exactp (z1) 53)
	        (and (= (gnorm) 0)
		     (= (snorm) 0))))
  :hints (("Goal" :in-theory (enable rnd-expshft-pos-13-b gnorm-rewrite snorm-rewrite)  
                  :use ((:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))))))

(local-defthmd rnd-expshft-pos-15-b
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (iff (exactp (abs (+ (a) (b))) 53)
	        (and (= (gnorm) 0)
		     (= (snorm) 0))))
  :hints (("Goal" :in-theory (e/d (z1) (abs))
                  :use (rnd-expshft-pos-14-b
		        (:instance exactp-shift (x (abs (+ (a) (b))))
			                        (k (- (+ 53 (1- (expt 2 10))) (expshft)))
						(n 53))))))

(defthmd rnd-expshft-pos-106
  (implies (and (= (mulovfl) 0) (not (= (expshft) 0)) (= (expo (sumshft)) 106))
           (and (>= (abs (+ (a) (b))) (spn (dp)))
	        (equal (rnd (abs (+ (a) (b))) (modep) 53)
	               (* (expt 2 (- (expshft) (+ (1- (expt 2 10)) 52)))
		          (sumnorm)))
	        (iff (equal (rnd (abs (+ (a) (b))) (modep) 53)
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0)))))
  :hints (("Goal" :use (rnd-expshft-pos-7 rnd-expshft-pos-12-b rnd-expshft-pos-15-b
                        (:instance rnd-exactp-b (x (abs (+ (a) (b)))) (mode (modep)) (n 53))))))

(local-defund z0 ()
  (* (expt 2 (+ 51 (expt 2 10)))
     (abs (+ (a) (b)))))

(local-in-theory (disable (z0)))

(local-defthm rationalp-z0
  (implies (= (mulovfl) 0)
           (rationalp (z0)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable expshft-rewrite z0))))

(local-defthm rnd-expshft-0-3
  (implies (and (= (mulovfl) 0) (= (expshft) 0))
           (and (>= (z0) (x1))
	        (< (z0) (1+ (x1)))
		(iff (= (z0) (x1)) (and (= (bits (sumshft) 52 0) 0) (= (stk) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (chop x1 z0 absval) (abs))
                  ;:nonlinearp t
                  :use (expshft-sumshft))))

(defthm abs-a+b<>0
  (not (= (abs (+ (a) (b))) 0))
  :rule-classes ()
  :hints (("Goal" :use a+b<>0)))

(local-defthm rnd-expshft-0-4
  (implies (and (= (mulovfl) 0) (= (expshft) 0))
           (and (= (fl (z0)) (x1))
	        (iff (integerp (z0)) (and (= (bits (sumshft) 52 0) 0) (= (stk) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bits x1 z0 absval) (abs))
                  ;:nonlinearp t
                  :use (abs-a+b<>0 rnd-expshft-0-3
		        (:instance mod-def (x (sumshft)) (y (expt 2 53)))))))

(local-defthmd rnd-expshft-0-8
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (equal (incnorm)
	          (if (roundup-pos (x1) (e1) (stk1) (modep) 53) 1 0)))
  :hints (("Goal" :in-theory (enable fpscr-rc roundup-pos rnddir computernddir modep
                              lnorm-rewrite gnorm-rewrite snorm-rewrite rndinfo-lemma signout
			      bits-x1 bitn-x1 expo-x1 expo-sumshft incnorm* rmode mode flip-mode)
                  :use (stk-0-1
		        (:instance bitn-plus-bits (x (sumshft)) (n 54) (m 0))
		        (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))
		        (:instance bitn-plus-bits (x (sumshft)) (n 54) (m 53))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd rnd-expshft-0-9
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (equal (rnd (z0) (modep) 53)
	          (if (= (incnorm) 0)
		      (rtz (x1) 53)
		    (fp+ (rtz (x1) 53) 53))))
  :hints (("Goal" :in-theory (enable rnd-expshft-0-8)
                  :use (expo-x1 stk-0-1 rnd-expshft-0-3 rnd-expshft-0-4
		        (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n 53))
		        (:instance expo-lower-bound (x (x1)))))))

(local-defthmd rnd-expshft-0-10
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (equal (rnd (z0) (modep) 53)
	          (* 2
		     (+ (bits (sumshft) 107 54) (incnorm)))))
  :hints (("Goal" :in-theory (enable bits-x1 expo-x1 rnd-expshft-0-9)
                  :use (incnorm-0-1 rnd-5 rnd-6
			(:instance bitn-plus-bits (x (sumshft)) (n 107) (m 54))
			(:instance bitn>expo (x (sumshft)) (n 107))))))

(local-defthmd rnd-expshft-0-11
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (equal (rnd (z0) (modep) 53)
	          (* 2 (sumnorm))))
  :hints (("Goal" :in-theory (enable rnd-expshft-0-10 sumunrnd sumnorm bits-bits bvecp)
                  :use (incnorm-0-1
		        (:instance bits-bounds (x (sumshft)) (i 106) (j 54))
			(:instance bitn-plus-bits (x (sumshft)) (n 107) (m 54))
			(:instance bitn>expo (x (sumshft)) (n 107))))))
			
(local-defthmd rnd-expshft-0-12
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (equal (rnd (abs (+ (a) (b))) (modep) 53)
	          (* (expt 2 (- (+ (expt 2 10) 50)))
		     (sumnorm))))
  :hints (("Goal" :in-theory (e/d (z0) (abs))
                  :use (rnd-expshft-0-11
		        (:instance rnd-shift (x (abs (+ (a) (b)))) (mode (modep))
			                     (n 53) (k (+ 51 (expt 2 10))))))))

(local-defthmd rnd-expshft-0-13
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (iff (exactp (z0) 53)
	        (and (= (bits (sumshft) 53 0) 0)
		     (= (stk) 0))))
  :hints (("Goal" :in-theory (enable bitn-x1 bits-x1)
                  :use (expo-x1 stk-0-1 rnd-expshft-0-3 rnd-expshft-0-4
			(:instance bitn-plus-bits (x (sumshft)) (n 54) (m 53))
			(:instance bitn-plus-bits (x (sumshft)) (n 54) (m 0))
			(:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))
		        (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n 53))
		        (:instance expo-lower-bound (x (x1)))))))

(local-defthmd rnd-expshft-0-14
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (iff (exactp (z0) 53)
	        (and (= (gnorm) 0)
		     (= (snorm) 0))))
  :hints (("Goal" :in-theory (enable rnd-expshft-0-13 gnorm-rewrite snorm-rewrite)  
                  :use ((:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))))))

(local-defthmd rnd-expshft-0-15
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (iff (exactp (abs (+ (a) (b))) 53)
	        (and (= (gnorm) 0)
		     (= (snorm) 0))))
  :hints (("Goal" :in-theory (e/d (z0) (abs))
                  :use (rnd-expshft-0-14
		        (:instance exactp-shift (x (abs (+ (a) (b))))
			                        (k (+ 51 (expt 2 10)))
						(n 53))))))

(defthmd rnd-expshft-0-norm
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (= (expo (sumshft)) 106))
           (and (>= (abs (+ (a) (b))) (spn (dp)))
	        (equal (rnd (abs (+ (a) (b))) (modep) 53)
	               (* (expt 2 (- (+ (expt 2 10) 50)))
		          (sumnorm)))
	        (iff (equal (rnd (abs (+ (a) (b))) (modep) 53)
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0)))))
  :hints (("Goal" :in-theory (disable abs)
                  :use (rnd-expshft-pos-7 rnd-expshft-0-12 rnd-expshft-0-15
                        (:instance rnd-exactp-b (x (abs (+ (a) (b)))) (mode (modep)) (n 53))))))

(local-defthmd rnd-expshft-0-expo
  (implies (and (= (mulovfl) 0) (< (expo (sumshft)) 106))
           (<= (x1) (1- (expt 2 53))))
  :hints (("Goal" :nonlinearp t :use ((:instance expo-upper-bound (x (sumshft))))
                  :in-theory (enable x1 chop))))

(local-defthmd rnd-expshft-0-7
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106))
           (< (abs (+ (a) (b))) (spn (dp))))
  :hints (("Goal" :in-theory (e/d (chop x1 absval spn dp) (abs))
                  :nonlinearp t
                  :use (expshft-sumshft rnd-expshft-0-expo))))

(local-defthmd rnd-expshft-0-8-b
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (incnorm)
	          (if (roundup-pos (x1) (e1) (stk1) (modep) (e1)) 1 0)))
  :hints (("Goal" :in-theory (enable fpscr-rc roundup-pos rnddir computernddir modep
                              lnorm-rewrite gnorm-rewrite snorm-rewrite rndinfo-lemma
			      bits-x1 bitn-x1 expo-x1 incnorm* rmode mode signout flip-mode)
                  :use (stk-0-1
		        (:instance bitn-plus-bits (x (sumshft)) (n 54) (m 0))
		        (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))
		        (:instance bitn-plus-bits (x (sumshft)) (n 54) (m 53))
		        (:instance bits-plus-bitn (x (sumshft)) (n 106) (m 53))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd rnd-expshft-0-9-b
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (rnd (z0) (modep) (e1))
	          (if (= (incnorm) 0)
		      (rtz (x1) (e1))
		    (fp+ (rtz (x1) (e1)) (e1)))))
  :hints (("Goal" :in-theory (enable rnd-expshft-0-8-b)
                  :nonlinearp t
                  :use (stk-0-1 rnd-expshft-0-3 rnd-expshft-0-4 expo-x1
		        (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n (e1)))			
		        (:instance expo-lower-bound (x (x1)))))))

(local-defthmd rnd-5-0
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (rtz (x1) (e1))
	          (* 2
		     (bits (x1) (e1) 1))))
  :hints (("Goal" :in-theory (enable x1) :use ((:instance bits-rtz (x (x1)) (n (1+ (e1))) (k (e1)))))))

(local-defthmd rnd-6-0
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (fp+ (rtz (x1) (e1)) (e1))
	          (* 2 (1+ (bits (x1) (e1) 1)))))
  :hints (("Goal" :in-theory (e/d (x1 fp+) (expo-rtz))
                  :use (expo-x1 rnd-5-0 (:instance expo-rtz (x (x1)) (n (e1)))))))

(defthmd bits>expo
  (implies (and (natp x)
                (integerp m)
                (integerp n)
                (>= m (1+ (expo x))))
           (equal (bits x n m) 0))
  :hints (("goal" :in-theory (e/d (bvecp) (bits-tail))
                  :nonlinearp t
                  :use (expo-upper-bound
		        (:instance bits-bits (i (expo x)) (j 0) (k n) (l m))
		        (:instance bits-tail (i (expo x)))))))

(local-defthmd rnd-expshft-0-10-b
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (rnd (z0) (modep) (e1))
	          (* 2 (+ (bits (sumshft) 107 54) (incnorm)))))
  :hints (("Goal" :in-theory (enable bits-x1 bits>expo)
                  :use (expo-x1 incnorm-0-1 rnd-5-0 rnd-6-0 rnd-expshft-0-9-b
		        (:instance bits-plus-bits (x (sumshft)) (n 107) (m 54) (p (+ 54 (e1))))))))

(local-defthm natp-x1
  (implies (= (mulovfl) 0) (natp (x1)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable x1))))

(local-defthmd rnd-expshft-0-11-b
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (rnd (z0) (modep) (e1))
	          (* 2 (sumnorm))))
  :hints (("Goal" :in-theory (enable bvecp bits>expo expo-x1 sumunrnd sumnorm bits-bits bvecp)
                  :nonlinearp t
                  :use (incnorm-0-1 rnd-expshft-0-10-b
		        (:instance bits-plus-bits (x (sumshft)) (n 107) (p 106) (m 54))
			(:instance bits-bounds (x (sumshft)) (i 105) (j 54))
		        (:instance bits-bounds (x (sumshft)) (i (+ 53 (e1))) (j 54))
			(:instance bits>expo (x (x1)) (n 107) (m (+ 54 (e1))))
			(:instance bits-plus-bits (x (x1)) (n 107) (m 54) (p (+ 54 (e1))))))))
			
(local-defthmd rnd-expshft-0-12-b
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (rnd (abs (+ (a) (b))) (modep) (e1))
	          (* (expt 2 (- (+ (expt 2 10) 50)))
		     (sumnorm))))
  :hints (("Goal" :in-theory (e/d (z0) (abs))
                  :use (rnd-expshft-0-11-b
		        (:instance rnd-shift (x (abs (+ (a) (b)))) (mode (modep))
			                     (n (e1)) (k (+ 51 (expt 2 10))))))))

(local-defthmd rnd-expshft-0-13-b
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (iff (exactp (z0) (e1))
	        (and (= (bits (sumshft) 53 0) 0)
		     (= (stk) 0))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable bitn-x1 bits-x1)
                  :use (stk-0-1 rnd-expshft-0-3 rnd-expshft-0-4 expo-x1
		        (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))
		        (:instance roundup-pos-thm (mode (modep)) (z (z0)) (n (e1)))
		        (:instance expo-lower-bound (x (x1)))))))

(local-defthmd rnd-expshft-0-14-b
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (iff (exactp (z0) (e1))
	        (and (= (gnorm) 0)
		     (= (snorm) 0))))
  :hints (("Goal" :in-theory (enable gnorm-rewrite snorm-rewrite)  
                  :use (rnd-expshft-0-13-b (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))))))

(local-defthmd rnd-expshft-0-15-b
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (iff (exactp (abs (+ (a) (b))) (e1))
	        (and (= (gnorm) 0)
		     (= (snorm) 0))))
  :hints (("Goal" :in-theory (e/d (z0) (abs))
                  :use (rnd-expshft-0-14-b
		        (:instance exactp-shift (x (abs (+ (a) (b))))
			                        (n (e1)) (k (+ 51 (expt 2 10))))))))

(local-defthmd rnd-expshft-0-16-a
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (> (expo (x1)) 0))
  :hints (("Goal" :nonlinearp t 
	          :use (rnd-expshft-0-3 expo-x1))))

(local-defthmd rnd-expshft-0-16
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (expo (z0)) (e1)))
  :hints (("Goal" :nonlinearp t 
	          :use (rnd-expshft-0-3 rnd-expshft-0-16-a
                        (:instance expo-upper-bound (x (x1)))
                        (:instance expo-lower-bound (x (x1)))
			(:instance expo-unique (x (z0)) (n (e1)))))))

(local-defthm rnd-expshft-0-17
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (expo (abs (+ (a) (b)))) (- (e1) (+ 51 (expt 2 10)))))
  :hints (("Goal" :in-theory (e/d (z0) (abs))
                  :use (abs-a+b<>0 rnd-expshft-0-16 (:instance expo-shift (x (z0)) (n (- (+ 51 (expt 2 10)))))))))

(local-defthmd rnd-expshft-0-18
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (equal (drnd (abs (+ (a) (b))) (modep) (dp))
	          (* (expt 2 (- (+ (expt 2 10) 50)))
		     (sumnorm))))
  :hints (("Goal" :in-theory (e/d (drnd dp spn) (abs))
                  :use (rnd-expshft-0-12-b))))

(local-defthmd rnd-expshft-0-19
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106) (>= (expo (sumshft)) 54))
           (and (equal (drnd (abs (+ (a) (b))) (modep) (dp))
	               (* (expt 2 (- (+ (expt 2 10) 50)))
		          (sumnorm)))
	        (iff (exactp (abs (+ (a) (b))) (e1))
	             (and (= (gnorm) 0)
		          (= (snorm) 0)))))
  :hints (("Goal" :use (rnd-expshft-0-15-b rnd-expshft-0-18))))

(local-defthmd rnd-expshft-0-20-a
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54))
           (< (x1) 2))
  :hints (("Goal" :use ((:instance expo>= (x (sumshft)) (n 54))) :nonlinearp t
                  :in-theory (enable x1 chop))))

(local-defthmd rnd-expshft-0-20
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54))
           (< (abs (+ (a) (b))) (spd (dp))))
  :hints (("Goal" :use (rnd-expshft-0-3 rnd-expshft-0-20-a) :nonlinearp t
                  :in-theory (e/d (z0 spd dp) (abs)))))

(local-defthmd rnd-expshft-0-21
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54))
           (equal (sumunrnd) 0))
  :hints (("Goal" :in-theory (enable sumunrnd bits>expo))))

(local-defthmd rnd-expshft-0-22
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54))
           (equal (sumnorm) (incnorm)))
  :hints (("Goal" :in-theory (enable rnd-expshft-0-21 sumnorm)
                  :use (incnorm-0-1))))

(local-defthmd rnd-expshft-0-23
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54))
           (equal (* (expt 2 (- (+ 50 (expt 2 10)))) (sumnorm))
	          (if (= (incnorm) 1) (spd (dp)) 0)))
  :hints (("Goal" :in-theory (enable rnd-expshft-0-22 spd dp)
                  :use (incnorm-0-1))))

(local-defthmd rnd-expshft-0-24
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54))
           (equal (bits (sumshft) 53 0) (sumshft)))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use ((:instance expo>= (x (sumshft)) (n 54))))))

(local-defthmd rnd-expshft-0-25
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (> (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (> (z0) 1))
  :hints (("Goal" :in-theory (e/d (z0 spd dp) (abs))
                  :nonlinearp t)))

(local-defthmd rnd-expshft-0-26-a
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54)); (> (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (iff (= (x1) 0) (= (bitn (sumshft) 53) 0)))
  :hints (("Goal" :in-theory (enable bvecp x1 chop) :nonlinearp t
                  :use ((:instance expo>= (x (sumshft)) (n 54))
		        (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))
			(:instance bits-bounds (x (sumshft)) (i 52) (j 0))))))

(local-defthmd rnd-expshft-0-26
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (> (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (and (= (gnorm) 1) (= (snorm) 1)))
  :hints (("Goal" :in-theory (enable rnd-expshft-0-24 gnorm-rewrite snorm-rewrite)
                  :use (rnd-expshft-0-26-a rnd-expshft-0-3 stk-0-1 rnd-expshft-0-25))))
		  
(local-defthmd rnd-expshft-0-27
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (> (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (iff (= (incnorm) 1)
	        (member (modep) '(rne rup))))
  :hints (("Goal" :in-theory (enable incnorm* rndinfo-lemma rnddir computernddir modep mode flip-mode fpscr-rc rmode signout)
		  :use (rnd-expshft-0-26 (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))		        

(local-defthmd rnd-expshft-0-28
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (> (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (and (= (gnorm) 1) (= (snorm) 1)
	        (not (= (drnd (abs (+ (a) (b))) (modep) (dp)) (abs (+ (a) (b)))))
		(= (drnd (abs (+ (a) (b))) (modep) (dp))
		   (* (expt 2 (- (+ 50 (expt 2 10)))) (sumnorm)))))
  :hints (("Goal" :in-theory (e/d (rnd-expshft-0-22 fpscr-rc spd dp rnddir computernddir modep mode flip-mode fpscr-rc rmode) (abs))
		  :use (rnd-expshft-0-20 rnd-expshft-0-26 rnd-expshft-0-27 incnorm-0-1
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))
			(:instance drnd-tiny-c (x (abs (+ (a) (b)))) (f (dp)) (mode (modep)))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd rnd-expshft-0-29
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (< (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (and (< (z0) 1) (= (x1) 0)))
  :hints (("Goal" :in-theory (e/d (z0 spd dp) (abs)) :use (rnd-expshft-0-3)
                  :nonlinearp t)))

(local-defthmd rnd-expshft-0-30
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (< (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (and (= (gnorm) 0) (= (snorm) 1)))
  :hints (("Goal" :in-theory (e/d (z0 rnd-expshft-0-24 gnorm-rewrite snorm-rewrite) (abs)) :nonlinearp t
                  :use (rnd-expshft-0-26-a rnd-expshft-0-3 stk-0-1 rnd-expshft-0-29 abs-a+b<>0))))

(local-defthmd rnd-expshft-0-31
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (< (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (iff (= (incnorm) 1)
	        (= (modep) 'rup)))
  :hints (("Goal" :in-theory (enable incnorm* rndinfo-lemma rnddir computernddir modep flip-mode signout mode fpscr-rc rmode)
		  :use (rnd-expshft-0-30 (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd rnd-expshft-0-32
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (< (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (and (= (gnorm) 0) (= (snorm) 1)
	        (not (= (drnd (abs (+ (a) (b))) (modep) (dp)) (abs (+ (a) (b)))))
		(= (drnd (abs (+ (a) (b))) (modep) (dp))
		   (* (expt 2 (- (+ 50 (expt 2 10)))) (sumnorm)))))
  :hints (("Goal" :in-theory (enable rnd-expshft-0-22 fpscr-rc spd dp rnddir computernddir modep mode signout flip-mode fpscr-rc rmode)
		  :use (rnd-expshft-0-20 rnd-expshft-0-30 rnd-expshft-0-31 incnorm-0-1 a+b<>0
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))
			(:instance drnd-tiny-a (x (abs (+ (a) (b)))) (f (dp)) (mode (modep)))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthm rnd-expshft-0-33
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (= (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (equal (z0) 1))
  :hints (("Goal" :in-theory (e/d (z0 spd dp) (abs))
                  :nonlinearp t)))

(local-defthmd rnd-expshft-0-34
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (= (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (and (= (lnorm) 0) (= (gnorm) 1) (= (snorm) 0)))
  :hints (("Goal" :in-theory (enable rnd-expshft-0-24 lnorm-rewrite gnorm-rewrite snorm-rewrite)
                  :use (rnd-expshft-0-26-a rnd-expshft-0-3 stk-0-1 rnd-expshft-0-33
		        (:instance bitn>expo (x (sumshft)) (n 54))))))

(local-defthmd rnd-expshft-0-35
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (= (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (iff (= (incnorm) 1)
	        (= (modep) 'rup)))
  :hints (("Goal" :in-theory (enable incnorm* rndinfo-lemma rnddir computernddir modep flip-mode fpscr-rc signout mode rmode)
		  :use (rnd-expshft-0-34 (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthmd rnd-expshft-0-36
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 54) (= (abs (+ (a) (b))) (/ (spd (dp)) 2)))
           (and (= (gnorm) 1) (= (snorm) 0)
	        (not (= (drnd (abs (+ (a) (b))) (modep) (dp)) (abs (+ (a) (b)))))
		(= (drnd (abs (+ (a) (b))) (modep) (dp))
		   (* (expt 2 (- (+ 50 (expt 2 10)))) (sumnorm)))))
  :hints (("Goal" :in-theory (e/d (rnd-expshft-0-22 fpscr-rc spd dp rnddir computernddir modep flip-mode fpscr-rc mode signout rmode) (abs))
		  :use (rnd-expshft-0-20 rnd-expshft-0-34 rnd-expshft-0-35 incnorm-0-1
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))
			(:instance drnd-tiny-c (x (abs (+ (a) (b)))) (f (dp)) (mode (modep)))
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(defthmd rnd-expshft-0-denorm
  (implies (and (= (mulovfl) 0) (= (expshft) 0) (< (expo (sumshft)) 106))
           (and (< (abs (+ (a) (b))) (spn (dp)))
	        (equal (drnd (abs (+ (a) (b))) (modep) (dp))
	               (* (expt 2 (- (+ (expt 2 10) 50)))
		          (sumnorm)))
	        (iff (equal (drnd (abs (+ (a) (b))) (modep) (dp))
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0)))))
  :hints (("Goal" :in-theory (e/d (expo-x1 dp) (abs))
                  :use (abs-a+b<>0 rnd-expshft-0-7 rnd-expshft-0-19 rnd-expshft-0-28 rnd-expshft-0-32 rnd-expshft-0-36
		        (:instance drnd-exactp-c (x (abs (+ (a) (b)))) (f (dp)) (mode (modep)))))))

(local-defthm ovfl-1
  (implies (= (expo (sumshft)) 107)
           (equal (bitn (sumunrnd) 53) 1))
  :hints (("Goal" :in-theory (enable sumunrnd bitn-bits)
                  :use ((:instance bitn-expo (x (sumshft)))))))

(local-defthm ovfl-2
  (implies (and (= (expo (sumshft)) 107) (= (ovfl2) 0))
           (equal (expo (sumovfl)) 52))
  :hints (("Goal" :in-theory (enable sumovfl ovfl2 bvecp)
                  :use (incovfl-0-1
		        (:instance expo-unique (x (sumovfl)) (n 52))
		        (:instance bitn-plus-bits (x (sumunrnd)) (n 53) (m 1))
		        (:instance bits-bounds (x (sumunrnd)) (i 53) (j 1))))))

(local-defthm ovfl-3
  (implies (and (= (expo (sumshft)) 107) (= (ovfl2) 1))
           (equal (sumovfl) (expt 2 53)))
  :hints (("Goal" :in-theory (enable sumovfl ovfl2 bvecp)
                  :use (incovfl-0-1
		        (:instance expo-unique (x (sumovfl)) (n 52))
		        (:instance bitn-plus-bits (x (sumunrnd)) (n 53) (m 1))
		        (:instance bits-bounds (x (sumunrnd)) (i 53) (j 1))))))

(local-defthmd ovfl-4
  (equal (ovfl) (bitn (+ (sumunrnd) (incnorm)) 53))
  :hints (("Goal" :in-theory (enable ovfl sumnorm bitn-bits))))

(local-defthmd ovfl-5
  (implies (and (= (expo (sumshft)) 107) (= (ovfl2) 0) (= (ovfl) 0))
           (> (expo (+ (sumunrnd) (incnorm))) 53))
  :hints (("Goal" :in-theory (enable ovfl-4 sumunrnd bvecp)
                  :use (incnorm-0-1 ovfl-1
		        (:instance bitn-plus-bits (x (sumunrnd)) (n 53) (m 0))
		        (:instance bitn-expo (x (+ (sumunrnd) (incnorm))))
		        (:instance expo>= (x (+ (sumunrnd) (incnorm))) (n 53))))))

(local-defthmd ovfl-6
  (implies (and (= (expo (sumshft)) 107) (= (ovfl2) 0) (= (ovfl) 0))
           (and (equal (sumunrnd) (1- (expt 2 54)))
	        (equal (incnorm) 1)))
  :hints (("Goal" :in-theory (enable sumunrnd bvecp)
                  :use (incnorm-0-1 ovfl-5
		        (:instance expo<= (x (+ (sumunrnd) (incnorm))) (n 53))
		        (:instance bits-bounds (x (sumshft)) (i 107) (j 54))))))

(local-defthmd ovfl-7
  (implies (and (= (expo (sumshft)) 107) (= (ovfl2) 0) (= (ovfl) 0))
           (equal (incovfl) 0))
  :hints (("Goal" :in-theory (enable ovfl2)
                  :use (incovfl-0-1 ovfl-6))))

(local-defthmd ovfl-8
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 107) (= (ovfl2) 0) (= (ovfl) 0))
           (not (equal (rnddir) 2)))
  :hints (("Goal" :in-theory (enable incnorm* incovfl* rndinfo-lemma gnorm-rewrite snorm-rewrite sovfl-rewrite)
                  :use (ovfl-6 ovfl-7 (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))))))

(local-defthmd ovfl-9
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 107) (= (ovfl2) 0) (= (ovfl) 0))
           (not (equal (rnddir) 0)))
  :hints (("Goal" :in-theory (enable incnorm* incovfl* rndinfo-lemma govfl-rewrite lnorm-rewrite
                                     sumunrnd gnorm-rewrite snorm-rewrite sovfl-rewrite)
                  :use (ovfl-6 ovfl-7
		        (:instance bitn-bits (x (sumshft)) (k 0) (i 107) (j 54))
		        (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))))))

(local-defthm ovfl-10
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 107))
           (or (= (ovfl2) 1) (= (ovfl) 1)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable ovfl2 ovfl incnorm* rndinfo-lemma)
                  :use (ovfl-6 ovfl-8 ovfl-9))))

(defthm ovfl-107
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 107))
           (and (implies (= (ovfl2) 0)
	                 (equal (expo (sumovfl)) 52))
                (implies (= (ovfl2) 1)
                         (equal (sumovfl) (expt 2 53)))
                (or (= (ovfl2) 1) (= (ovfl) 1))))
  :rule-classes ()
  :hints (("Goal" :use (ovfl-2 ovfl-3 ovfl-10))))

(local-defthm ovfl-11
  (implies (= (expo (sumshft)) 106)
           (equal (bitn (sumunrnd) 53) 0))
  :hints (("Goal" :in-theory (enable sumunrnd bitn-bits)
                  :use ((:instance bitn>expo (n 107) (x (sumshft)))))))

(local-defthm ovfl-12
  (implies (= (expo (sumshft)) 106)
           (equal (ovfl2) 0))
  :hints (("Goal" :in-theory (enable ovfl2)
                  :use ((:instance bitn-bits (x (sumunrnd)) (i 53) (j 1) (k 52))))))

(local-defthm ovfl-13
  (implies (= (expo (sumshft)) 106)
           (equal (bitn (sumunrnd) 52) 1))
  :hints (("Goal" :in-theory (enable sumunrnd bitn-bits)
                  :use ((:instance bitn-expo (x (sumshft)))))))

(local-defthm ovfl-14
  (implies (= (expo (sumshft)) 106)
           (equal (bitn (sumshft) 107) 0))
  :hints (("Goal" :in-theory (enable sumunrnd bitn-bits)
                  :use ((:instance bitn>expo (n 107) (x (sumshft)))))))

(local-defthm ovfl-15
  (implies (= (expo (sumshft)) 106)
           (equal (bitn (sumshft) 106) 1))
  :hints (("Goal" :in-theory (enable sumunrnd bitn-bits)
                  :use ((:instance bitn-expo (x (sumshft)))))))

(local-defthm ovfl-16
  (implies (= (expo (sumshft)) 106)
           (and (<= (sumnorm) (expt 2 53))
	        (>= (sumnorm) (expt 2 52))))
  :hints (("Goal" :in-theory (enable sumunrnd sumnorm bvecp)
                  :use (incnorm-0-1
		        (:instance bitn-plus-bits (x (sumshft)) (n 107) (m 54))
		        (:instance bitn-plus-bits (x (sumshft)) (n 106) (m 54))
		        (:instance bits-bounds (x (sumshft)) (i 105) (j 54))))))

(local-defthm ovfl-17
  (implies (and (= (expo (sumshft)) 106) (= (ovfl) 0))
           (equal (expo (sumnorm)) 52))
  :hints (("Goal" :in-theory (enable ovfl)
                  :use (ovfl-16
                        (:instance expo>= (x (sumnorm)) (n 52))
                        (:instance expo<= (x (sumnorm)) (n 53))
			(:instance bitn-expo (x (sumnorm)))))))

(local-defthmd ovfl-18
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 106) (= (ovfl) 1))
           (equal (sumnorm) (expt 2 53)))
  :hints (("Goal" :in-theory (enable ovfl bvecp)
                  :use (ovfl-16
		        (:instance bitn-plus-bits (x (sumnorm)) (n 53) (m 0))))))

(local-defthmd ovfl-19
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 106) (= (ovfl) 1))
           (and (equal (sumunrnd) (1- (expt 2 53)))
	        (equal (incnorm) 1)))
  :hints (("Goal" :in-theory (enable sumnorm sumunrnd)
                  :use (ovfl-18 incnorm-0-1
		        (:instance bits-bounds (x (sumshft)) (i 106) (j 54))
			(:instance bitn-plus-bits (x (sumshft)) (n 107) (m 54))))))

(local-defthmd ovfl-20
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 106) (= (ovfl) 1))
           (equal (govfl) 1))
  :hints (("Goal" :in-theory (enable govfl-rewrite sumunrnd)
                  :use (ovfl-19 (:instance bitn-bits (x (sumshft)) (i 107) (j 54) (k 0))))))

(local-defthm ovfl-21
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 106) (= (ovfl) 1))
           (and (member (rnddir) '(0 2))
	        (or (= (gnorm) 1) (= (snorm) 1))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable gnorm-rewrite snorm-rewrite incnorm* rndinfo-lemma)
                  :use (ovfl-19))))

(local-defthmd ovfl-22
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 106) (= (ovfl) 1))
           (equal (sovfl) 1))
  :hints (("Goal" :in-theory (enable gnorm-rewrite snorm-rewrite sovfl-rewrite)
                  :use (ovfl-21 (:instance bitn-plus-bits (x (sumshft)) (n 53) (m 0))))))

(local-defthmd ovfl-23
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 106) (= (ovfl) 1))
           (equal (incovfl) 1))
  :hints (("Goal" :in-theory (enable incovfl* rndinfo-lemma)
                  :use (ovfl-22 ovfl-21))))

(local-defthmd ovfl-24
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 106) (= (ovfl) 1))
           (equal (sumovfl) (expt 2 52)))
  :hints (("Goal" :in-theory (enable sumovfl)
                  :use (ovfl-19 ovfl-23))))

(defthm ovfl-106
  (implies (and (= (mulovfl) 0) (= (expo (sumshft)) 106))
           (and (= (ovfl2) 0)
                (implies (= (ovfl) 0)
                         (equal (expo (sumnorm)) 52))
	        (implies (= (ovfl) 1)
                         (and (equal (sumnorm) (expt 2 53))
			      (equal (sumovfl) (expt 2 52))
			      (equal (govfl) 1)
			      (or (= (gnorm) 1) (= (snorm) 1))))))
  :rule-classes ()
  :hints (("Goal" :use (ovfl-12 ovfl-17 ovfl-18 ovfl-20 ovfl-21 ovfl-24))))

(local-defthmd ovfl-25
  (implies (and (= (mulovfl) 0) (< (expo (sumshft)) 106))
           (< (sumunrnd) (expt 2 52)))
  :hints (("Goal" :in-theory (enable sumunrnd)
                  :use ((:instance bits-plus-bits (x (sumshft)) (n 107) (p 106) (m 54))
		        (:instance bits>expo (x (sumshft)) (n 107) (m 106))
			(:instance bits-bounds (x (sumshft)) (i 105) (j 54))))))

(defthmd ovfl-denorm
  (implies (and (= (mulovfl) 0) (< (expo (sumshft)) 106))
           (and (= (ovfl2) 0)
	        (= (ovfl) 0)
		(<= (sumnorm) (expt 2 52))))
  :hints (("Goal" :in-theory (enable ovfl2 ovfl sumnorm bvecp)
                  :use (ovfl-25 incnorm-0-1
		        (:instance bits-plus-bitn (x (sumunrnd)) (n 53) (m 0))))))
