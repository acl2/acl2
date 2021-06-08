(in-package "RTL")

(include-book "rtl/rel11/lib/top" :dir :system)
(include-book "fadd64")
(local (include-book "round"))
(local (include-book "special"))

(local-defthmd ovfl-1
  (implies (= (mulovfl) 1)
           (>= (abs (b)) (expt 2 1025)))
  :hints (("Goal" :use (comp-constraints-lemma)
           :in-theory (enable opblong mulovfl comp-constraints))))

(local-defthmd expa-bound
  (<= (expa) (- (expt 2 11) 2))
  :hints (("Goal" :use (comp-constraints-lemma)
           :in-theory (enable expf dp expnt checkdenorm opaz opax expa comp-constraints))))

(local-defthmd expb-bound
  (implies (= (fma) 0)
           (<= (expb) (- (expt 2 11) 2)))
  :hints (("Goal" :use (comp-constraints-lemma)
           :in-theory (enable expf dp expnt checkdenorm opbz expb comp-constraints))))

(local-defthmd ovfl-2
  (< (abs (a)) (expt 2 1024))
  :hints (("Goal" :use (bvecp-siga expa-bound)
                  :in-theory (enable bvecp a val absval)
		  :nonlinearp t)))

(local-defthmd ovfl-3
  (implies (= (mulovfl) 1)
           (>  (abs (+ (a) (b))) (expt 2 1024)))
  :hints (("Goal" :use (ovfl-1 ovfl-2))))

(local-defthmd ovfl-4
  (implies (= (mulovfl) 1)
           (and (>=  (expo (rnd (abs (+ (a) (b))) (modep) 53)) 1024)
	        (= (informax) 1)))
  :hints (("Goal" :in-theory (enable informax)
                  :use (ovfl-3
                        (:instance expo>= (x (abs (+ (a) (b)))) (n 1024))
			(:instance expo-rnd (x (abs (+ (a) (b)))) (mode (modep)) (n 53))))))

(local-defthmd signb-rewrite-2
  (implies (not (= (b) 0))
           (equal (signb)
                  (if (< (b) 0) 1 0)))
  :hints (("Goal" :use (comp-constraints-lemma)
           :in-theory (enable signb-rewrite comp-constraints))))

(local-defthmd signout-rewrite
  (equal (signout)
         (if (> (+ (a) (b)) 0) 0 1))
  :hints (("Goal" :in-theory (enable sign signout signl-rewrite signb-rewrite-2)
		  :use (signb-rewrite ovfl-1 ovfl-2))))

(local-defthmd rnd-modep-rmode-2
  (equal (rnd (+ (a) (b)) (mode) 53)
         (if (= (signout) 0)
             (rnd (abs (+ (a) (b))) (modep) 53)
           (- (rnd (abs (+ (a) (b))) (modep) 53))))
  :hints (("Goal" :in-theory (enable modep signout-rewrite)
                  :use ((:instance rnd-minus (x (abs (+ (a) (b)))) (mode (mode)) (n 53))))))

(local-defthmd ovfl-5
  (implies (= (mulovfl) 1)
           (and (>=  (expo (rnd (+ (a) (b)) (mode) 53)) 1024)
	        (= (informax) 1)))
  :hints (("Goal" :use (ovfl-4 rnd-modep-rmode-2))))

(local-defthmd ovfl-8
  (implies (and (= (mulovfl) 0) (= (expshft) 0))
           (< (sumshft) (expt 2 108)))
  :hints (("Goal" :in-theory (enable sumshft)
                  :use ((:instance bits-bounds (x (ash (sum) (lshift))) (i 107) (j 0))))))

(local-defthmd ovfl-9
  (implies (and (= (mulovfl) 0) (= (expshft) 0))
           (< (abs (+ (a) (b))) 100))
  :hints (("Goal" :in-theory (e/d (absval chop) (abs))
                  :use (ovfl-8 expshft-sumshft))))

(local-defthm expo-rnd-bound
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0)
		  (common-mode-p mode))
	     (<= (expo (rnd x mode n))
		 (1+ (expo x))))
  :rule-classes ()
  :hints (("Goal" :use (expo-rnd (:instance expo-minus  (x (rnd x mode n)))))))

(local-defthmd ovfl-10
  (implies (and (= (mulovfl) 0) (= (expshft) 0))
           (and (<  (expo (rnd (abs (+ (a) (b))) (modep) 53)) 1024)
	        (= (informax) 0)))
  :hints (("Goal" :in-theory (e/d (informax) ()) :nonlinearp t
                  :use (ovfl-9
		        (:instance expo-rnd-bound (x (abs (+ (a) (b)))) (mode (modep)) (n 53))
			(:instance expo<= (x (abs (+ (a) (b)))) (n 1022))))))

(local-defthmd inz-rewrite
  (implies (and (= (mulovfl) 0) (= (fma) 1))
           (equal (inz)
                  (if (and (= (expb) 0) (= (fracb) 0) (= (mulstk) 0))
                      1 0)))
  :hints (("Goal" :use (comp-constraints-lemma b-0)
           :in-theory (enable mulovfl opblong mulstk frac fracb expf dp expnt checkdenorm opbz expb comp-constraints))))

(local-defthmd ovfl-11
  (implies (and (= (fma) 1) (= (mulovfl) 0) (= (opblong) 0))
           (equal (b) 0))
  :hints (("Goal" :use (expb-0-b) :in-theory (enable opblong inz-rewrite bp absval val sigb))))

(local-defthmd ovfl-12
  (implies (and (= (fma) 1) (= (mulovfl) 0) (= (opblong) 0))
           (>= (abs (a)) (absval (expshft) (chop (sumshft) -53))))
  :hints (("Goal" :use (expshft-sumshft)
                  :in-theory (enable ovfl-11))))

(local-defthmd ovfl-13-a
  (implies (and (= (fma) 1) (= (mulovfl) 0) (>= (expo (sumshft)) 106))
           (>= (chop (sumshft) -53) (expt 2 106)))
  :hints (("Goal" :in-theory (enable chop)
		  :use ((:instance expo-lower-bound (x (sumshft))))
		  :nonlinearp t)))

(local-defthmd ovfl-13
  (implies (and (= (fma) 1) (= (mulovfl) 0) (= (opblong) 0) (= (expshft) 2047) (>= (expo (sumshft)) 106))
           (>= (abs (a)) (expt 2 1024)))
  :hints (("Goal" :in-theory (enable absval)
		  :use (ovfl-12 ovfl-13-a)
		  :nonlinearp t)))

(local-defthmd ovfl-14
  (implies (and (= (fma) 1) (= (mulovfl) 0))
           (< (abs (a)) (expt 2 1024)))
  :hints (("Goal" :use (expa-bound (:instance bits-bounds (x (frac (opaz))) (i 104) (j 0)))
                  :in-theory (enable bvecp a siga absval val cat fraca)
		  :nonlinearp t)))

(local-defthmd fma-0-1
  (bitp (fma))
  :hints (("Goal" :use (comp-constraints-lemma)
           :in-theory (enable comp-constraints))))

(local-defthm ovfl-15
  (implies (and (= (mulovfl) 0) (= (expshft) 2047) (>= (expo (sumshft)) 106))
           (equal (opblong) 1))
  :hints (("Goal" :in-theory (enable expshft-rewrite expl-rewrite opblong)
		  :use (fma-0-1 expa-bound expb-bound ovfl-13 ovfl-14))))

(local-defthmd bvecp-expshft
  (implies (= (mulovfl) 0)
           (bvecp (expshft) 11))
  :hints (("Goal" :in-theory (enable expshft-rewrite expa expb expl bvecp expnt cat far-rewrite)  
                  :use ((:instance bits-bounds (x (opbz)) (i 115) (j 105))
		        (:instance bits-bounds (x (opaz)) (i 115) (j 105))))))

(local-defthmd ovfl-16
  (implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 107) (= (ovfl2) 1))
           (equal (expo (rnd (abs (+ (a) (b))) (modep) 53))
	          (- (expshft) 1021)))
  :hints (("Goal" :use (rnd-expshft-pos-107 ovfl-107
                        (:instance expo-shift (x (sumovfl)) (n (- (expshft) (+ (1- (expt 2 10)) 51))))))))

(local-defthmd ovfl-17
  (implies (and (= (mulovfl) 0) (>= (expshft) 2045))
           (member (expshft) '(2045 2046 2047)))
  :hints (("Goal" :use (bvecp-expshft) :in-theory (enable bvecp))))

(local-defthmd ovfl-18
(implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 107) (= (ovfl2) 1))
           (iff (<  (expo (rnd (abs (+ (a) (b))) (modep) 53)) 1024)
	        (= (informax) 0)))
  :hints (("Goal" :in-theory (e/d (informax) (abs))
                  :use (ovfl-16 bvecp-expshft ovfl-17))))

(local-defthmd ovfl-19
  (implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 107) (= (ovfl2) 0) (= (ovfl) 1))
           (equal (expo (rnd (abs (+ (a) (b))) (modep) 53))
	          (- (expshft) 1022)))
  :hints (("Goal" :use (rnd-expshft-pos-107 ovfl-107
                        (:instance expo-shift (x (sumovfl)) (n (- (expshft) (+ (1- (expt 2 10)) 51))))))))

(local-defthmd ovfl-17
  (implies (and (= (mulovfl) 0) (>= (expshft) 2045))
           (member (expshft) '(2045 2046 2047)))
  :hints (("Goal" :use (bvecp-expshft) :in-theory (enable bvecp))))

(local-defthmd ovfl-21
(implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 107) (= (ovfl2) 0) (= (ovfl) 1))
           (iff (<  (expo (rnd (abs (+ (a) (b))) (modep) 53)) 1024)
	        (= (informax) 0)))
  :hints (("Goal" :in-theory (e/d (informax) (abs))
                  :use (ovfl-19 bvecp-expshft))))

(local-defthmd ovfl-22
  (implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 107))
           (iff (<  (expo (rnd (abs (+ (a) (b))) (modep) 53)) 1024)
	        (= (informax) 0)))
  :hints (("Goal" :in-theory (enable ovfl2)
                  :use (ovfl-18 ovfl-21 ovfl-107))))

(local-defthmd ovfl-23
  (implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 106) (= (ovfl) 1))
           (equal (expo (rnd (abs (+ (a) (b))) (modep) 53))
	          (- (expshft) 1022)))
  :hints (("Goal" :use (rnd-expshft-pos-106 ovfl-106
                        (:instance expo-shift (x (sumovfl)) (n (- (expshft) (+ (1- (expt 2 10)) 52))))))))

(local-defthmd ovfl-24
(implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 106) (= (ovfl) 1))
           (iff (<  (expo (rnd (abs (+ (a) (b))) (modep) 53)) 1024)
	        (= (informax) 0)))
  :hints (("Goal" :in-theory (e/d (informax) (abs))
                  :use (ovfl-23 ovfl-106 bvecp-expshft))))

(local-defthmd ovfl-25
  (implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 106) (= (ovfl) 0))
           (equal (expo (rnd (abs (+ (a) (b))) (modep) 53))
	          (- (expshft) 1023)))
  :hints (("Goal" :use (rnd-expshft-pos-106 ovfl-106
                        (:instance expo-shift (x (sumnorm)) (n (- (expshft) (+ (1- (expt 2 10)) 52))))))))

(local-defthmd ovfl-26
  (implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 106) (= (ovfl) 0))
           (iff (<  (expo (rnd (abs (+ (a) (b))) (modep) 53)) 1024)
	        (= (informax) 0)))
  :hints (("Goal" :in-theory (e/d (informax) (abs))
                  :use (ovfl-25 ovfl-106 bvecp-expshft))))

(local-defthmd ovfl-27
  (implies (and (= (mulovfl) 0) (> (expshft) 0) (= (expo (sumshft)) 106))
           (iff (<  (expo (rnd (abs (+ (a) (b))) (modep) 53)) 1024)
	        (= (informax) 0)))
  :hints (("Goal" :in-theory (enable ovfl)
                  :use (ovfl-24 ovfl-26))))

(local-defthmd ovfl-28
  (implies (and (= (mulovfl) 0) (> (expshft) 0))
           (member (expo (sumshft)) '(106 107)))
  :hints (("Goal" :use (expshft>0-sumshft
                        (:instance expo<= (x (sumshft)) (n 107))
			(:instance bits-bounds (x (ash (sum) (lshift))) (i 107) (j 0)))
		  :in-theory (enable fl sumshft))))

(local-defthmd ovfl-29
  (implies (= (mulovfl) 0)
           (equal (informax)
                  (if (< (expo (rnd (+ (a) (b)) (mode) 53)) 1024) 0 1)))
  :hints (("Goal" :use (ovfl-4 ovfl-10 ovfl-22 ovfl-27 ovfl-28 rnd-modep-rmode)
                  :in-theory (disable abs))))

(local-defthmd ovfl-30-a
  (iff (>= (expo (rnd (abs (+ (a) (b))) (modep) 53)) 1024)
       (> (rnd (abs (+ (a) (b))) (modep) 53) (lpn (dp))))
  :hints (("Goal" :use ((:instance expo>= (x (rnd (abs (+ (a) (b))) (modep) 53)) (n 1024))
                        (:instance expo<= (x (rnd (abs (+ (a) (b))) (modep) 53)) (n 1023))
			(:instance fp+2 (y (rnd (abs (+ (a) (b))) (modep) 53)) (x (lpn (dp))) (n 53)))
	          :in-theory (e/d (lpn dp) (abs)))))

(local-defthmd ovfl-30
  (iff (>= (expo (rnd (+ (a) (b)) (mode) 53)) 1024)
       (> (abs (rnd (+ (a) (b)) (mode) 53)) (lpn (dp))))
  :hints (("Goal" :use (ovfl-30-a rnd-modep-rmode-2))))

(local-defthmd ovfl-29-a
  (equal (informax)
         (if (<= (abs (rnd (+ (a) (b)) (mode) 53)) (lpn (dp))) 0 1))
  :hints (("Goal" :in-theory (enable dp lpn ovfl-29) :use (ovfl-5 ovfl-30))))

(local-defthm bitn-rin-12-0
  (equal (bitn (rin) 12) 0)
  :hints (("Goal" :use (comp-constraints-lemma
                        (:instance bitn-bits (x (rin)) (i 12) (j 10) (k 2)))
                  :in-theory (enable comp-constraints))))

(local-defthm bitn-rin-11-0
  (equal (bitn (rin) 11) 0)
  :hints (("Goal" :use (comp-constraints-lemma
                        (:instance bitn-bits (x (rin)) (i 12) (j 10) (k 1)))
                  :in-theory (enable comp-constraints))))

(local-defthm bitn-rin-10-0
  (equal (bitn (rin) 10) 0)
  :hints (("Goal" :use (comp-constraints-lemma
                        (:instance bitn-bits (x (rin)) (i 12) (j 10) (k 0)))
                  :in-theory (enable comp-constraints))))

(local-defthmd ovfl-31
  (let* ((rmode (fpscr-rc (rin)))
         (r (rnd (+ (a) (b)) rmode 53))
         (sgn (if (< (+ (a) (b)) 0) 1 0)))
    (declare (ignore sgn))
    (implies (and (= (informax) 1) (= (isspecial) 0)
                  (or (and (eql rmode 'rdn) (> r 0))
                      (and (eql rmode 'rup) (< r 0))
                      (eql rmode 'rtz)))
             (equal (d) (nencode (* (sgn r) (lpn (dp))) (dp)))))
  :hints (("Goal" :use (a+b<>0 (:instance sgn-rnd (x (+ (a) (b))) (mode (fpscr-rc (rin))) (n 53)))
                  :in-theory (enable d sgn rmode signout-rewrite fpscr-rc dp sigw expw nencode expout fracout rnddir computernddir))))

(local-defthmd ovfl-32
  (let* ((rmode (fpscr-rc (rin)))
         (r (rnd (+ (a) (b)) rmode 53))
         (sgn (if (< (+ (a) (b)) 0) 1 0)))
    (implies (and (= (isspecial) 0)
                  (= (informax) 1) 
                  (not (or (and (eql rmode 'rdn) (> r 0))
                           (and (eql rmode 'rup) (< r 0))
                           (eql rmode 'rtz))))
             (equal (d) (iencode sgn (dp)))))
  :hints (("Goal" :use (a+b<>0 (:instance sgn-rnd (x (+ (a) (b))) (mode (fpscr-rc (rin))) (n 53)))
                  :in-theory (enable rmode signout-rewrite d sgn signl-rewrite fpscr-rc dp sigw expw iencode expout fracout
                              rnddir computernddir))))

(local-defthm ofc-ufc-piz
  (implies (not (= (fma) 0))
           (and (= (piz) 0) (= (bitn (mulexcps) 3) 0) (= (bitn (mulexcps) 2) 0)))
  :hints (("Goal" :in-theory (enable comp-constraints) :use (comp-constraints-lemma))))

(local-defthmd ovfl-33
  (implies (and (= (isspecial) 0) (= (informax) 1))
           (equal (bitn (flags) 3)
	          (bitn (set-flag (ofc) (set-flag (ixc) 0)) (ufc))))
  :hints (("Goal" :in-theory (enable checkspecial checkdenorm bitn-bits bitn-logior set-flag flags flags-5 flags-4 flags-3 flags-2 flags-1))))

(local-defthmd ovfl-34
  (implies (and (= (isspecial) 0) (= (informax) 1))
           (equal (bitn (flags) 2)
	          (bitn (set-flag (ofc) (set-flag (ixc) (rin))) (ofc))))
  :hints (("Goal" :in-theory (enable checkspecial checkdenorm bitn-bits bitn-logior set-flag flags flags-5 flags-4 flags-3 flags-2 flags-1))))

(local-defthmd ovfl-35
  (implies (and (= (isspecial) 0) (= (informax) 1))
           (equal (bitn (flags) 4)
	          (bitn (set-flag (ofc) (set-flag (ixc) (rin))) (ixc))))
  :hints (("Goal" :in-theory (enable checkspecial checkdenorm bitn-bits bitn-logior set-flag flags flags-5 flags-4 flags-3 flags-2 flags-1))))

(local-defthm bitn-set-flag
  (implies (and (natp k)
                (natp b)
		(natp r))
           (equal (bitn (set-flag b r) k)
	          (if (= k b) 1 (bitn r k))))
  :hints (("Goal" :use ((:instance bitn-logior (x (expt 2 b)) (y r) (n k)))
                  :in-theory (enable bitn-expt bitn-expt-0 set-flag))))

(local-defthm natp-set-flag
  (implies (and (natp r) (natp b))
           (natp (set-flag b r)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable set-flag))))

(local-defthm int-flags
  (integerp (flags))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable flags flags-5 flags-4 flags-3 flags-2 flags-1 checkspecial checkdenorm))))

(local-in-theory (disable flags))

(local-defthm overflow-case
  (implies (and (= (isspecial) 0) (= (informax) 1))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (ovfl-33 ovfl-34 ovfl-35
                        (:instance sgn-rnd (x (+ (a) (b))) (mode (fpscr-rc (rin))) (n 53)))
                  :in-theory (enable ovfl-29-a ovfl-31 ovfl-32 dp bitn-bits rmode sgn
		                     mode bitn-logior signout-rewrite fpscr-rc))))

(local-defthm unfl-1
  (implies (= (informax) 0)
           (equal (mulovfl) 0))
  :hints (("Goal" :use (ovfl-5))))

(local-defthmd unfl-2
  (implies (= (informax) 0)
           (iff (>= (abs (+ (a) (b))) (spn (dp)))
	        (member (expo (sumshft)) '(106 107))))
  :hints (("Goal" :use (expshft>0-sumshft expshft=0-sumshft expo-sumshft rnd-expshft-pos-107 rnd-expshft-pos-106
                        rnd-expshft-0-norm rnd-expshft-0-denorm))))

(local-defthmd unfl-3
  (implies (= (informax) 0)
           (iff (>= (abs (+ (a) (b))) (spn (dp)))
	        (or (= (bitn (sumshft) 107) 1)
		    (= (bitn (sumshft) 106) 1))))
  :hints (("Goal" :use (unfl-2 expshft>0-sumshft expshft=0-sumshft
                        (:instance bitn-expo (x (sumshft)))
                        (:instance bitn-expo (x (sumshft)))
                        (:instance bitn>expo (x (sumshft)) (n 107))
                        (:instance bitn>expo (x (sumshft)) (n 106)))
                  :in-theory (e/d (expo-sumshft) (abs)))))

(local-defthmd unfl-4
  (implies (= (informax) 0)
           (equal (tiny)
	          (if (< (abs (+ (a) (b))) (spn (dp))) 1 0)))
  :hints (("Goal" :use (unfl-3 (:instance bitn-0-1 (x (sumshft)) (n 107)) (:instance bitn-0-1 (x (sumshft)) (n 106)))
                  :in-theory (e/d (sumunrnd bitn-bits tiny) (abs)))))

(local-defthmd unfl-4-1
  (implies (and (= (fma) 1) (= (inz) 1))
           (equal (bitn (mulexcps) 4) 0))
  :hints (("Goal" :in-theory (enable absval val comp-constraints opblong mulstk mulovfl)
                  :use (inz-rewrite comp-constraints-lemma))))

(local-defthm flags-4-post-comp
  (and (equal (bitn (flags-4) 2) 0)
       (equal (bitn (flags-4) 3) 0)
       (equal (bitn (flags-4) 4) 0))
  :hints (("Goal" :in-theory (enable opblong mulovfl bitn-bits checkspecial checkdenorm flags-4 flags-3 flags-2 flags-1)
                  :use (inz-rewrite unfl-4-1))))

(local-defthm unfl-5
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 1)
		(= (bitn (rin) (fz)) 1))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (a+b<>0)
                  :in-theory (enable ovfl-29-a unfl-4 dp d bitn-bits nencode rmode iencode expout fracout rnddir mode fzp
		                     bitn-logior flags flags-5 nencode computernddir signl-rewrite signout-rewrite fpscr-rc))))

(local-defthmd unfl-6
  (implies (= (informax) 0)
           (equal (tiny)
	          (if (< (expo (sumshft)) 106) 1 0)))
  :hints (("Goal" :use (unfl-4 rnd-expshft-pos-107 rnd-expshft-pos-106 rnd-expshft-0-norm rnd-expshft-0-denorm
                        expo-sumshft expshft=0-sumshft expshft>0-sumshft))))

(local-defthmd unfl-7
  (implies (and (= (informax) 0)
                (= (tiny) 1))
	   (and (equal (drnd (abs (+ (a) (b))) (modep) (dp))
	               (* (expt 2 (- (+ (expt 2 10) 50)))
		          (sumnorm)))
	        (iff (equal (drnd (abs (+ (a) (b))) (modep) (dp))
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0)))))
  :hints (("Goal" :use (rnd-expshft-0-denorm unfl-6 expshft>0-sumshft))))

(local-defthmd unfl-7-a
  (implies (and (= (informax) 0)
                (= (tiny) 1))
	   (and (equal (abs (drnd (+ (a) (b)) (mode) (dp)))
	               (* (expt 2 (- (+ (expt 2 10) 50)))
		          (sumnorm)))
	        (iff (equal (abs (drnd (+ (a) (b)) (mode) (dp)))
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0)))))
  :hints (("Goal" :use (unfl-7 drnd-modep-rmode))))

(local-defthmd unfl-8
  (implies (and (= (informax) 0)
                (= (tiny) 1))
	   (iff (= (bitn (sumnorm) 52) 1)
	        (= (sumnorm) (expt 2 52))))
  :hints (("Goal" :in-theory (enable unfl-6 bvecp)
                  :use (ovfl-denorm 
                        (:instance bitn-plus-bits (x (sumnorm)) (n 52) (m 0))
			(:instance bits-bounds (x (sumnorm)) (i 51) (j 0))))))

(local-defthmd unfl-9
  (implies (and (= (informax) 0)
                (= (tiny) 1))
	   (iff (= (bitn (sumnorm) 52) 1)
	        (= (abs (drnd (+ (a) (b)) (mode) (dp)))
		   (spn (dp)))))
  :hints (("Goal" :in-theory (enable spn dp) :use (unfl-7 unfl-8 drnd-modep-rmode))))

(local-defthmd unfl-10
  (implies (and (= (informax) 0)
                (= (tiny) 1))
           (equal (inxnorm)
	          (if (= (drnd (+ (a) (b)) (mode) (dp)) (+ (a) (b)))
		      0 1)))
  :hints (("Goal" :in-theory (enable inxnorm* rndinfo-lemma drnd-modep-rmode signl-rewrite)
                  :use (unfl-7))))

(local-defthmd unfl-11
  (implies (and (= (informax) 0)
                (= (tiny) 1))
           (not (equal (abs (+ (a) (b))) (spn (dp)))))
  :hints (("Goal" :in-theory (enable inxnorm* rndinfo-lemma drnd-modep-rmode signl-rewrite)
                  :use (unfl-4))))

(local-defthm unfl-12
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 1)
		(= (bitn (rin) (fz)) 0)
		(= (bitn (sumnorm) 52) 1))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (a+b<>0 unfl-9 unfl-11)
                  :in-theory (enable drnd ovfl-29-a unfl-4 dp d bitn-logior mode bitn-bits nencode rmode expout fracout rnddir
		                     fzp flags-5 flags computernddir signl-rewrite signout-rewrite fpscr-rc))))

(local-defthm drnd-non-positive
  (implies (and (<= x 0)
                (rationalp x)
                (formatp f)
                (common-mode-p mode))
           (<= (drnd x mode f) 0))
  :hints (("Goal" :in-theory (enable drnd)))
  :rule-classes (:type-prescription))

(local-defthm drnd-non-negative
  (implies (and (>= x 0)
                (rationalp x)
                (formatp f)
                (> n 0)
                (common-mode-p mode))
           (>= (rnd x mode f) 0))
  :hints (("Goal" :in-theory (enable drnd)))
  :rule-classes (:type-prescription))

(local-defthm unfl-13
  (implies (and (= (informax) 0)
                (= (tiny) 1))
	   (equal (expshft) 0))
  :hints (("Goal" :use (unfl-4 rnd-expshft-pos-107 rnd-expshft-pos-106 rnd-expshft-0-norm rnd-expshft-0-denorm
                        expo-sumshft expshft=0-sumshft expshft>0-sumshft))))

(local-defthm unfl-14
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 1)
		(= (bitn (rin) (fz)) 0)
		(= (bitn (sumnorm) 52) 0)
		(= (drnd (+ (a) (b)) (mode) (dp)) 0))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (a+b<>0 unfl-9 unfl-11 unfl-7-a)
                  :in-theory (enable ovfl-29-a unfl-4 dp d flags bitn-bits dencode rmode expout fracout rnddir
		                     unfl-10 sgn flags-5 mode fzp bitn-logior computernddir signout-rewrite fpscr-rc))))

(local-defthm rmode-common
  (common-mode-p (mode))
  :hints (("Goal" :in-theory (enable mode rmode fpscr-rc common-mode-p)
                  :use ((:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(local-defthm unfl-15
  (implies (and (= (informax) 0)
                (= (tiny) 1)
		(= (bitn (rin) (fz)) 0)
		(= (bitn (sumnorm) 52) 0)
		(not (= (drnd (+ (a) (b)) (mode) (dp)) 0)))
           (equal (sumnorm)
	          (* (expt 2 1074) (abs (drnd (+ (a) (b)) (mode) (dp))))))
  :rule-classes ()
  :hints (("Goal" :use (unfl-7-a))))

(local-defthm unfl-16
  (implies (and (= (informax) 0)
                (= (tiny) 1)
		(= (bitn (rin) (fz)) 0)
		(= (bitn (sumnorm) 52) 0)
		(not (= (drnd (+ (a) (b)) (mode) (dp)) 0)))
           (equal (abs (drnd (+ (a) (b)) (mode) (dp)))
	          (* (expt 2 (expo (drnd (+ (a) (b)) (mode) (dp))))
		     (sig (drnd (+ (a) (b)) (mode) (dp))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fp-abs (x (drnd (+ (a) (b)) (mode) (dp))))))))

(local-defthmd unfl-17
  (implies (and (= (informax) 0)
                (= (tiny) 1)
		(= (bitn (rin) (fz)) 0)
		(= (bitn (sumnorm) 52) 0)
		(not (= (drnd (+ (a) (b)) (mode) (dp)) 0)))
           (equal (sumnorm)
	          (* (expt 2 (+ 1074 (expo (drnd (+ (a) (b)) (mode) (dp)))))
		     (sig (drnd (+ (a) (b)) (mode) (dp))))))
  :hints (("Goal" :use (unfl-15 unfl-16))))

(local-defthmd unfl-18
  (implies (and (= (informax) 0)
                (= (tiny) 1)
		(= (bitn (sumnorm) 52) 0))
	   (bvecp (sumnorm) 52))
  :hints (("Goal" :use (ovfl-denorm
                        (:instance bits-bounds (x (sumnorm)) (i 51) (j 0))
                        (:instance bitn-plus-bits (x (sumnorm)) (n 53) (m 0))
                        (:instance bitn-plus-bits (x (sumnorm)) (n 52) (m 0)))
		  :in-theory (enable unfl-6 bvecp))))

(local-defthm unfl-19
  (implies (and (= (informax) 0)
                (= (tiny) 1)
		(= (bitn (sumnorm) 52) 0))
           (EQUAL (BINARY-CAT 2048 12 (SUMNORM) 52)
                  (BINARY-CAT 1 1 (SUMNORM) 63)))
  :hints (("Goal" :use (unfl-18) :in-theory (enable cat))))

(local-defthm unfl-20
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 1)
                (= (bitn (rin) (fz)) 0)
		(= (bitn (sumnorm) 52) 0)
		(not (= (drnd (+ (a) (b)) (mode) (dp)) 0)))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (a+b<>0 unfl-9 unfl-11 unfl-7-a unfl-17 unfl-18)
                  :in-theory (enable ovfl-29-a unfl-4 dp d flags bitn-bits dencode rmode expout fracout rnddir mode fzp
		                     bitn-logior drnd bvecp cat-0 unfl-10 sgn flags-5 computernddir signout-rewrite fpscr-rc))))

(local-defthm underflow-case
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 1))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (unfl-20 unfl-14 unfl-12 unfl-5
                        (:instance bitn-0-1 (x (rin)) (n (fz)))
			(:instance bitn-0-1 (x (sumnorm)) (n 52))))))

(local-defthmd norm-1
  (implies (and (= (informax) 0)
                (= (tiny) 0)
		(= (expo (sumshft)) 107))
	   (and (equal (rnd (abs (+ (a) (b))) (modep) 53)
	               (* (expt 2 (- (expshft) (+ (1- (expt 2 10)) 51)))
		          (sumovfl)))
	        (iff (equal (rnd (abs (+ (a) (b))) (modep) 53)
		            (abs (+ (a) (b))))
	             (and (= (govfl) 0)
		          (= (sovfl) 0)))))
  :hints (("Goal" :use (rnd-expshft-pos-107 expshft=0-sumshft))))

(local-defthmd norm-2
  (implies (and (= (informax) 0)
                (= (tiny) 0)
		(= (expo (sumshft)) 107))
	   (and (equal (abs (rnd (+ (a) (b)) (mode) 53))
	               (* (expt 2 (- (expshft) (+ (1- (expt 2 10)) 51)))
		          (sumovfl)))
	        (iff (equal (abs (rnd (+ (a) (b)) (mode) 53))
		            (abs (+ (a) (b))))
	             (and (= (govfl) 0)
		          (= (sovfl) 0)))))
  :hints (("Goal" :in-theory (enable signl-rewrite) :use (a+b<>0 norm-1 rnd-modep-rmode))))

(local-defthmd norm-3
  (implies (and (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 1))
	   (and (equal (abs (rnd (+ (a) (b)) (mode) 53))
	               (expt 2 (- (expshft) 1021)))
	        (iff (equal (abs (rnd (+ (a) (b)) (mode) 53))
		            (abs (+ (a) (b))))
	             (and (= (govfl) 0)
		          (= (sovfl) 0)))))
  :hints (("Goal" :use (norm-2 ovfl-107 ovfl-106 ovfl-denorm expshft=0-sumshft expo-sumshft))))

(local-defthmd norm-4
  (implies (and (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 1))
	   (and (<= 0 (expshft)) (< (expshft) 2045)))
  :hints (("Goal" :in-theory (enable unfl-6 informax)
                  :use (ovfl-17 ovfl-107 ovfl-106 ovfl-denorm expshft=0-sumshft expo-sumshft))))

(local-defthmd norm-5
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 1))
           (equal (rnd (+ (a) (b)) (mode) 53)
	          (ndecode (d) (dp))))	          
  :hints (("Goal" :use (a+b<>0 norm-3 norm-4)
                  :in-theory (enable d ndecode expout fracout rnddir sgnf dp expf manf
		                     bvecp bvecp sgn computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-6
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 1))
           (normp (d) (dp)))
  :hints (("Goal" :use (a+b<>0 norm-3 norm-4)
                  :in-theory (enable d normp encodingp expout fracout rnddir sgnf dp expf manf
		                     bvecp bvecp sgn computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-7
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 1))
           (equal (d) (nencode (rnd (+ (a) (b)) (mode) 53) (dp))))
  :hints (("Goal" :in-theory (enable norm-5 norm-6))))

(local-defthmd norm-8
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (expo (sumshft)) 107))
           (equal (inxovfl)
	          (if (= (rnd (+ (a) (b)) (mode) 53) (+ (a) (b)))
		      0 1)))
  :hints (("Goal" :in-theory (enable inxovfl* rndinfo-lemma)
                  :use (norm-2))))

(local-defthm norm-9
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 1))
	   (equal (expo (sumshft)) 107))
  :hints (("Goal" :use (ovfl-17 ovfl-107 ovfl-106 ovfl-denorm expshft=0-sumshft expo-sumshft))))

(local-defthm norm-10
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 1))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (a+b<>0 unfl-9 unfl-11 unfl-7-a unfl-17 unfl-18)
                  :in-theory (enable ovfl-29-a unfl-4 dp d flags bitn-bits dencode rmode expout fracout rnddir mode bitn-logior
		                     fzp norm-7 norm-8 bvecp cat-0 unfl-10 sgn flags-5 computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-11
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1))
	   (and (<= 0 (expshft)) (< (expshft) 2046)))
  :hints (("Goal" :in-theory (enable unfl-6 informax)
                  :use (ovfl-17 ovfl-107 ovfl-106 ovfl-denorm expshft=0-sumshft expo-sumshft))))

(local-defthmd norm-12
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 107))
	   (equal (sumovfl) (+ (expt 2 52) (fracout))))
  :hints (("Goal" :in-theory (enable bvecp fracout)
                  :use (ovfl-107 expshft=0-sumshft
		        (:instance bitn-expo (x (sumovfl)))
		        (:instance expo-upper-bound (x (sumovfl)))
		        (:instance bitn-plus-bits (x (sumovfl)) (n 52) (m 0))))))

(local-defthmd norm-13
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 107))
	   (equal (expout) (1+ (expshft))))
  :hints (("Goal" :in-theory (enable bvecp expout)
                  :use (ovfl-107 expshft=0-sumshft norm-11))))

(local-defthmd norm-14
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 107))
           (equal (rnd (+ (a) (b)) (mode) 53)
	          (ndecode (d) (dp))))	          
  :hints (("Goal" :use (a+b<>0 norm-2 norm-11)
                  :in-theory (enable d ndecode norm-12 norm-13 rnddir sgnf dp expf manf
		                     fracout bvecp bvecp sgn computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-15
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 107))
           (normp (d) (dp)))
  :hints (("Goal" :use (a+b<>0 norm-2 norm-11)
                  :in-theory (enable d normp encodingp expout fracout rnddir sgnf dp expf manf
		                     bvecp bvecp sgn computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-16
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 107))
           (equal (d) (nencode (rnd (+ (a) (b)) (mode) 53) (dp))))
  :hints (("Goal" :in-theory (enable norm-14 norm-15))))

(local-defthm norm-17
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 107))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (a+b<>0 unfl-9 unfl-11 unfl-7-a unfl-17 unfl-18)
                  :in-theory (enable ovfl-29-a unfl-4 dp flags bitn-bits dencode rmode expout fracout rnddir bitn-logior mode
		                     norm-16 norm-8 bvecp cat-0 unfl-10 sgn flags-5 computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-18
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (expo (sumshft)) 106))
	   (and (equal (rnd (abs (+ (a) (b))) (modep) 53)
	               (* (expt 2 (- (if (= (expshft) 0) 1 (expshft)) (+ (1- (expt 2 10)) 52)))
		          (sumnorm)))
	        (iff (equal (rnd (abs (+ (a) (b))) (modep) 53)
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0)))))
  :hints (("Goal" :use (rnd-expshft-pos-106 rnd-expshft-0-norm expshft=0-sumshft))))

(local-defthmd norm-19-a
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (expo (sumshft)) 106))
	   (equal (abs (rnd (+ (a) (b)) (mode) 53))
		  (rnd (abs (+ (a) (b))) (modep) 53)))
  :hints (("Goal" :in-theory (enable signout-rewrite) :use (a+b<>0 rnd-modep-rmode))))

(local-defthmd norm-19
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (expo (sumshft)) 106))
	   (and (equal (abs (rnd (+ (a) (b)) (mode) 53))
	               (* (expt 2 (- (if (= (expshft) 0) 1 (expshft)) (+ (1- (expt 2 10)) 52)))
		          (sumnorm)))
	        (iff (equal (abs (rnd (+ (a) (b)) (mode) 53))
		            (abs (+ (a) (b))))
	             (and (= (gnorm) 0)
		          (= (snorm) 0)))))
  :hints (("Goal"  :use (norm-18 norm-19-a) :in-theory (theory 'minimal-theory))))

(local-defthm norm-20
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 106))
           (equal (rnd (+ (a) (b)) (mode) 53)
	          (ndecode (d) (dp))))	          
  :hints (("Goal" :use (a+b<>0 norm-11 norm-19 ovfl-106)
                  :in-theory (enable d ndecode expout fracout rnddir sgnf dp expf manf
		                     bvecp bvecp sgn computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-21
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 106))
           (normp (d) (dp)))
  :hints (("Goal" :use (a+b<>0 norm-2 norm-11)
                  :in-theory (enable d normp encodingp expout fracout rnddir sgnf dp expf manf
		                     bvecp bvecp sgn computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-22
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 106))
           (equal (d) (nencode (rnd (+ (a) (b)) (mode) 53) (dp))))
  :hints (("Goal" :in-theory (enable norm-20 norm-21))))

(local-defthm norm-23
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 106))
	   (and (not (= (rnd (+ (a) (b)) (mode) 53) (+ (a) (b))))
	        (= (inxovfl) 1)))
  :rule-classes ()
  :hints (("Goal" :use (norm-19 ovfl-106)
                  :in-theory (enable inxovfl* rndinfo-lemma))))

(local-defthm norm-24
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 1)
                (= (expo (sumshft)) 106))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (a+b<>0 unfl-9 unfl-11 unfl-7-a unfl-17 unfl-18 norm-23)
                  :in-theory (enable ovfl-29-a unfl-4 dp flags bitn-bits rmode rnddir mode bitn-logior
		                     norm-22 bvecp cat-0 unfl-10 sgn flags-5 computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-25
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 0))
	   (and (equal (expo (sumshft)) 106)
                (equal (sumnorm) (+ (expt 2 52) (fracout)))))
  :hints (("Goal" :in-theory (enable unfl-6 bvecp fracout)
                  :use (ovfl-106 ovfl-107 expo-sumshft expshft=0-sumshft expshft>0-sumshft
		        (:instance bitn-expo (x (sumnorm)))
		        (:instance expo-upper-bound (x (sumnorm)))
		        (:instance bitn-plus-bits (x (sumnorm)) (n 52) (m 0))))))

(local-defthm norm-25-a
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 0))
	   (equal (bitn (sumnorm) 52) 1))
  :hints (("Goal" :in-theory (enable unfl-6 bvecp fracout)
                  :use (ovfl-106 ovfl-107 expo-sumshft expshft=0-sumshft expshft>0-sumshft
		        (:instance bitn-expo (x (sumnorm)))
		        (:instance expo-upper-bound (x (sumnorm)))
		        (:instance bitn-plus-bits (x (sumnorm)) (n 52) (m 0))))))

(local-defthmd norm-26
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (expo (sumshft)) 106))
           (equal (inxnorm)
	          (if (= (rnd (+ (a) (b)) (mode) 53) (+ (a) (b)))
		      0 1)))
  :hints (("Goal" :in-theory (enable inxnorm* rndinfo-lemma)
                  :use (norm-19))))

(local-defthmd norm-27
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 0))
	   (equal (expout) (if (= (expshft) 0) 1 (expshft))))
  :hints (("Goal" :in-theory (enable norm-25 bvecp expout)
                  :use (bvecp-expshft ovfl-106 expshft=0-sumshft norm-11 (:instance bitn-expo (x (sumnorm)))))))

(local-defthmd bvecp-fracout
  (bvecp (fracout) 52)
  :hints (("Goal" :in-theory (enable fracout))))

(local-defthmd norm-28
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 0))
           (equal (rnd (+ (a) (b)) (mode) 53)
	          (ndecode (d) (dp))))	          
  :hints (("Goal" :use (a+b<>0 norm-19 bvecp-fracout bvecp-expshft)
                  :in-theory (enable d ndecode rnddir sgnf dp expf manf frac
		                     norm-25 norm-27 bvecp sgn computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-29
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 0))
	   (and (integerp (expshft)) ; added by Matt K after tau bug fix 8/16/18
                (<= 0 (expshft))
                (<= (expshft) 2046)))
  :hints (("Goal" :in-theory (enable unfl-6 informax)
                  :use (ovfl-17 ovfl-107 ovfl-106 ovfl-denorm expshft=0-sumshft expo-sumshft))))

; Added by Matt K after tau bug fix 8/16/18:
(local (in-theory (disable INT-EXPSHFT)))

(local-defthmd norm-30
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 0))
           (normp (d) (dp)))
  :hints (("Goal" :use (a+b<>0 norm-29 norm-19)
                  :in-theory (enable d normp encodingp expout fracout rnddir sgnf dp expf manf
		                     bvecp bvecp sgn computernddir signout-rewrite fpscr-rc))))

(local-defthmd norm-31
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 0))
           (equal (d) (nencode (rnd (+ (a) (b)) (mode) 53) (dp))))
  :hints (("Goal" :in-theory (enable norm-28 norm-30))))

(local-defthm norm-32
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0)
		(= (ovfl2) 0)
		(= (ovfl) 0))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (a+b<>0 unfl-9 unfl-11 unfl-7-a unfl-17 unfl-18)
                  :in-theory (enable ovfl-29-a unfl-4 dp flags bitn-bits dencode rmode expout fracout rnddir norm-25 mode bitn-logior
		                     norm-26 norm-31 bvecp cat-0 unfl-10 sgn flags-5 computernddir signout-rewrite fpscr-rc))))

(local-defthmd bvecp-sumshft
  (bvecp (sumshft) 108)
  :hints (("Goal" :in-theory (enable sumshft)))) 

(local-defthm normal-case
  (implies (and (= (isspecial) 0)
                (= (informax) 0)
                (= (tiny) 0))
           (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
                   (and (equal (d) d-spec)
                        (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                        (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                        (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (norm-10 norm-17 bvecp-sumshft norm-24 norm-32
                        (:instance bitn-0-1 (x (sumnorm)) (n 53))
                        (:instance expo<= (x (sumshft)) (n 107)))
                  :in-theory (e/d (ovfl unfl-6 bvecp) (arm-post-comp)))))

(local-defthm general-case
  (mv-let (d-spec r-spec) (arm-post-comp (+ (a) (b)) (rin) (dp))
    (implies (= (isspecial) 0)
             (and (equal (d) d-spec)
                  (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
                  (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
                  (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (informax tiny) (arm-post-comp))
                  :use (overflow-case underflow-case normal-case))))

(local-defthmd a-opa-1
  (implies (not (and (= (bitn (rin) (fz)) 1) (= (expf (opa) (dp)) 0)))
           (equal (a)
                  (decode (opa) (dp))))
  :hints (("Goal" :in-theory (enable manf fraca frac sigf expf dp fzp opax expnt opaz checkdenorm a val absval signa expa siga
                                     bitn-bits sign cat sgnf decode ndecode ddecode)
		  :use ((:instance bits-shift-up-1 (k 53) (x (bits (opa) 63 0)) (i 115) (j 105))
		        (:instance bits-shift-up-1 (k 53) (x (bits (opa) 63 0)) (i 116) (j 105))
		        (:instance bitn-shift-up (k 53) (x (bits (opa) 63 0)) (n 63))
			(:instance bits-shift-up-2 (k 53) (x (bits (opa) 63 0)) (i 51))
			(:instance bits-shift-up-2 (k 1) (x (BITS (* 9007199254740992 (BITS (OPA) 63 0)) 104 0)) (i 104))))))

(local-defthmd a-opa-2
  (implies (and (= (bitn (rin) (fz)) 1) (= (expf (opa) (dp)) 0))
           (equal (fraca)
                  0))
  :hints (("Goal" :in-theory (enable manf fraca frac sigf expf dp fzp opax expnt opaz checkdenorm a val absval signa expa siga
                                     bitn-bits sign cat sgnf)
		  :use ((:instance bits-shift-up-1 (k 53) (x (bits (opa) 63 0)) (i 115) (j 105))
		        (:instance bits-shift-up-2 (k 105) (x (BITS (* 9007199254740992 (BITS (OPA) 63 0)) 116 105)) (i -1))))))

(local-defthmd a-opa-3
  (implies (and (= (bitn (rin) (fz)) 1) (= (expf (opa) (dp)) 0))
           (equal (siga)
                  0))
  :hints (("Goal" :in-theory (enable a-opa-2 siga expf dp expa expnt opaz checkdenorm opax))))

(local-defthmd a-opa-4
  (implies (and (= (bitn (rin) (fz)) 1) (= (expf (opa) (dp)) 0))
           (equal (a)
                  0))
  :hints (("Goal" :in-theory (enable a-opa-3 a val absval))))

(local-defthmd a-opa
  (equal (a)
         (if (and (= (bitn (rin) (fz)) 1) (= (expf (opa) (dp)) 0))
	     0
	   (decode (opa) (dp))))
  :hints (("Goal" :use (a-opa-1 a-opa-4))))

(local-defthm fadd64-comp-main
  (let ((a (if (and (= (bitn (rin) (fz)) 1) (= (expf (opa) (dp)) 0))
	       0
	     (decode (opa) (dp)))))
    (mv-let (d-spec r-spec) (arm-post-comp (+ a (b)) (rin) (dp))
      (and (equal (d) d-spec)
           (equal (bitn (logior (rin) (flags)) (ixc)) (bitn r-spec (ixc)))
           (equal (bitn (logior (rin) (flags)) (ufc)) (bitn r-spec (ufc)))
           (equal (bitn (logior (rin) (flags)) (ofc)) (bitn r-spec (ofc))))))
  :rule-classes ()
  :hints (("Goal" :use (general-case) :in-theory (e/d (isspecial-0 a-opa) (arm-post-comp)))))

(local-defthmd lemma-to-be-functionally-instantiated
  (mv-let (d flags) (fadd64 (opa) (opb) (bitn (rin) 24) (bitn (rin) 25) (bits (rin) 23 22)
                            (fma) (inz) (piz) (expovfl) (mulexcps))
    (let ((a (if (and (= (bitn (rin) 24) 1) (= (expf (opa) (dp)) 0))
	         0
	       (decode (opa) (dp)))))
      (mv-let (d-spec r-spec) (arm-post-comp (+ a (b)) (rin) (dp))
        (and (equal d d-spec)
             (equal (bitn (logior (rin) flags) (ixc)) (bitn r-spec (ixc)))
             (equal (bitn (logior (rin) flags) (ufc)) (bitn r-spec (ufc)))
             (equal (bitn (logior (rin) flags) (ofc)) (bitn r-spec (ofc)))))))
  :hints (("Goal" :use (fadd64-comp-main)
                  :in-theory (e/d (equivalence-lemma) (arm-post-comp)))))

(defund absval (e s)
  (if (> e 0)
      (* (expt 2 (- (- e (1- (expt 2 10))) 106)) s)
    (* (expt 2 (- (- 1 (1- (expt 2 10))) 106)) s)))

(defund val (b e s)
  (if (= b 0)
      (absval e s)
    (- (absval e s))))

(defund comp-constraints (opa opb rin fma inz piz expovfl mulexcps b)
  (let* ((mulovfl (if (and (= fma 1) (= inz 0)) expovfl 0))
         (mulstk (if (= fma 1) (bitn mulexcps 4) 0))
         (fz (bitn rin (fz)))
         (expa (expf opa (dp)))
         (a (if (and (= fz 1) (= expa 0)) 0 (decode opa (dp))))
         (signb (bitn opb 116))
         (expb (bits opb 115 105))
         (fracb (if (and (= fma 0) (= fz 1) (= expb 0)) 0 (bits opb 104 0)))
         (sigb (if (= expb 0) (* 2 fracb) (+ (expt 2 106) (* 2 fracb)))))
    (and (bvecp opa 64)
         (bvecp opb 117)
         (bvecp rin 32)
         (bvecp fma 1)
         (bvecp inz 1)
         (bvecp piz 1)
         (bvecp expovfl 1)
         (bvecp mulexcps 8)
         (rationalp b)
         (= (bits rin 12 10) 0)
         (< expa (1- (expt 2 11)))
	 (implies (= fma 0) (and (< expb (1- (expt 2 11))) (= (bits opb 52 0) 0)))
         (not (= (+ a b) 0))
         (implies (= fma 1) (and (= piz 0) (= (bitn mulexcps 3) 0) (= (bitn mulexcps 2) 0)))
         (implies (= fma 1) (= inz (if (= b 0) 1 0)))
         (implies (not (= b 0)) (= signb (if (< b 0) 1 0)))
         (cond ((= mulovfl 1)
	        (and (>= (abs b) (expt 2 (1+ (expt 2 10))))
	             (= mulstk 0)))
               ((> expb 0)
                (and (= mulstk 0)
                     (= b (val signb expb sigb))))
               (t
                (and (<= (absval expb (chop sigb -53)) (abs b))
                     (< (abs b) (absval expb (+ (chop sigb -53) (expt 2 53))))
                     (iff (= (absval expb (chop sigb -53)) (abs b))
                          (and (= (bits sigb 52 0) 0)
                               (= mulstk 0)))))))))          

(local (defmacro ic ()
  '(comp-constraints opa opb rin fma inz piz expovfl mulexcps b)))

(defthm fadd64-comp
  (implies (comp-constraints opa opb rin fma inz piz expovfl mulexcps b)
           (let* ((fz (bitn rin 24)) (dn (bitn rin 25)) (rmode (bits rin 23 22))
                  (a (if (and (= fz 1) (= (expf opa (dp)) 0)) 0 (decode opa (dp)))))
             (mv-let (d flags) (fadd64 opa opb fz dn rmode fma inz piz expovfl mulexcps)
               (mv-let (d-spec r-spec) (arm-post-comp (+ a b) rin (dp))
                 (and (equal d d-spec)
                      (equal (bitn (logior rin flags) (ixc)) (bitn r-spec (ixc)))
                      (equal (bitn (logior rin flags) (ufc)) (bitn r-spec (ufc)))
                      (equal (bitn (logior rin flags) (ofc)) (bitn r-spec (ofc))))))))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance lemma-to-be-functionally-instantiated
                         (opa (lambda () (if (ic) opa (opa))))
                         (opb (lambda () (if (ic) opb (opb))))
                         (rin (lambda () (if (ic) rin (rin))))
                         (fma (lambda () (if (ic) fma (fma))))
                         (inz (lambda () (if (ic) inz (inz))))
                         (piz (lambda () (if (ic) piz (piz))))
                         (expovfl (lambda () (if (ic) expovfl (expovfl))))
                         (mulexcps (lambda () (if (ic) mulexcps (mulexcps))))
			 (b (lambda () (if (ic) b (b)))))))
           ("Subgoal 1" :use (comp-constraints-lemma))))
