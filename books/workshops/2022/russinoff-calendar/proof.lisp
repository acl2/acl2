(in-package "RTL")

(local (include-book "rtl/rel11/lib/top" :dir :system))
(include-book "calendar")

;;-----------------------------------------------------------------------------------------------------------
;; Moments and moladot
;;-----------------------------------------------------------------------------------------------------------

;; A moment is determined by its three components:

(defun day (x) (ag 'day x))
(defun hour (x) (ag 'hour x))
(defun part (x) (ag 'part x))

;; The final conjunct ensures that a moment is uniquely determined by its fields:

(defund momentp (x)
  (and (natp (day x))
       (natp (hour x)) (< (hour x) 24)
       (natp (part x)) (< (part x) 1080)
       (= x (as 'day (day x) (as 'hour (hour x) (as 'part (part x) ()))))))

;; momentp is closed under timaplus and multime:

(defthm momentp+
  (implies (and (momentp x) (momentp y))
           (momentp (addtime x y)))
  :hints (("Goal" :in-theory (enable fl momentp day hour part addtime))))

(defthm momentp*
  (implies (and (natp n) (momentp x))
           (momentp (multime n x)))
  :hints (("Goal" :in-theory (enable fl momentp multime))))

;; Every molad or delayed-molad is a moment:

(defthm natp-priormonths
  (implies (natp n)
           (natp (molad-loop-0 y year n)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable molad-loop-0))))

(defthm momentp-molad
  (implies (posp y)
           (momentp (molad y)))
  :hints (("Goal" :in-theory (enable molad))))

(defthmd momentp-dmolad
  (implies (posp y)
           (momentp (dmolad y)))
  :hints (("Goal" :in-theory (enable dmolad))))

(defthm momentp-beharad
  (momentp (beharad))
  :hints (("Goal" :in-theory (enable momentp beharad))))

(defthm momentp-lunation
  (momentp (lunation))
  :hints (("Goal" :in-theory (enable momentp lunation))))

;; Total number of parts in a moment:

(defund expand (x)
  (+ (* 1080
        (+ (* 24 (day x))
           (hour x)))
     (part x)))

(defthm expand=
  (implies (and (momentp x) (momentp y) (= (expand x) (expand y)))
           (= x y))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (momentp expand) (ACL2::|(equal (mod (+ x y) z) x)|))
                  :use ((:instance mod-mult (m (part x)) (n 1080) (a (+ (hour x) (* 24 (day x)))))
			(:instance mod-mult (m (part y)) (n 1080) (a (+ (hour y) (* 24 (day y)))))
		        (:instance mod-mult (m (hour x)) (n 24) (a (day x)))
		        (:instance mod-mult (m (hour y)) (n 24) (a (day y)))))))

(defthmd expand+
  (implies (and (momentp x) (momentp y))
           (equal (expand (addtime x y))
	          (+ (expand x) (expand y))))
  :hints (("Goal" :in-theory (enable momentp addtime expand)
                  :use ((:instance mod-def (x (+ (part x) (part y))) (y 1080))
		        (:instance mod-def (x (+ (hour x) (hour y) (fl (/ (+ (part x) (part y)) 1080)))) (y 24))))))

(defthmd expand*
  (implies (and (natp m) (momentp x))
           (equal (expand (multime m x))
	          (* m (expand x))))
  :hints (("Goal" :in-theory (enable momentp multime expand)
                  :use ((:instance mod-def (x (* m (part x))) (y 1080))
		        (:instance mod-def (x (+ (* m (hour x)) (fl (/ (* m (part x)) 1080)))) (y 24))))))

;; molad-loop-0 decomposition:

(defthmd molad-loop-decomp
  (implies (and (natp prior)
		(posp y)
		(posp k)
		(posp year)
		(<= y k)
		(<= k year))
	   (equal (molad-loop-0 y year prior)
		  (molad-loop-0 k year (molad-loop-0 y k prior))))
  :hints (("Goal" :in-theory (enable molad-loop-0))))

;; Molad recurrence formula:

(defthmd molad-next
  (implies (posp y)
           (equal (molad (1+ y))
	          (addtime (molad y)
		           (multime (monthsinyear y) (lunation)))))
  :hints (("Goal" :in-theory (enable molad-loop-0 common monthsinyear molad expand+ expand*)
                  :expand ((molad-loop-0 y (+ 1 y) (molad-loop-0 1 y 0)))
                  :use ((:instance molad-loop-decomp (prior 0) (y 1) (year (1+ y)) (k y))
		        (:instance expand= (x (molad (1+ y)))
		                           (y (addtime (molad y) (multime (if1 (common y) 12 13) (lunation)))))))))

(defthmd dmolad-next
  (implies (posp y)
           (equal (dmolad (1+ y))
	          (addtime (dmolad y)
		            (multime (monthsinyear y) (lunation)))))
  :hints (("Goal" :in-theory (enable dmolad expand+ expand*)
                  :use (molad-next
		        (:instance expand= (x (dmolad (1+ y)))
		                           (y (addtime (dmolad y) (multime (monthsinyear y) (lunation)))))))))

(defthmd expand-dmolad-next
  (implies (posp y)
           (equal (expand (dmolad (1+ y)))
	          (+ (expand (dmolad y))
		     (* (monthsinyear y) (expand (lunation))))))
  :hints (("Goal" :in-theory (enable lunation expand+ expand*)
                  :use (dmolad-next momentp-dmolad
		        (:instance momentp-dmolad (y (1+ y)))))))


;;-----------------------------------------------------------------------------------------------------------
;; Admissibility of year lengths: first proof
;;-----------------------------------------------------------------------------------------------------------

;; First we establish a set of conditions sufficent to ensure that 2 years have the same length.
;; The proof is based on the following function, which derives the delay of RH of a given year y
;; from mod(y, 19) together with the day of the week and the time of day of the delayed molad of y:

(defund rh-delay (dw h p leap leap-1)
  (if1 (logior1 (logior1 (log= dw 1) (log= dw 4))
                (log= dw 6))
       1
       (if1 (logand1 (logand1 (log= dw 3)
                              (lognot1 (logior1 (log< h 15) (logand1 (log= h 15) (log< p 204)))))
                     (lognot1 leap))
            2
            (if1 (logand1 (logand1 (log= dw 2)
                                   (lognot1 (logior1 (log< h 21) (logand1 (log= h 21) (log< p 589)))))
                          leap-1)
                 1
                 0))))

(defthmd rh-rewrite
  (let ((dm (dmolad y)))
    (implies (posp y)
             (equal (roshhashanah y)
	            (+ (day dm)
		       (rh-delay (mod (day dm) 7) (hour dm) (part dm) (leap y) (leap (- y 1)))))))
  :hints (("Goal" :in-theory (enable dayofweek momentp roshhashanah earlier day hour part rh-delay)
                  :use (momentp-dmolad))))

;; We note that mod(y, 19) determones whether y, y - 1, or y + 1 is a leap year:

(defund leap-guts (m)
  (logior1 (logior1 (logior1 (logior1 (logior1 (logior1 (log= m 0) (log= m 3))
                                               (log= m 6))
                                      (log= m 8))
                             (log= m 11))
                    (log= m 14))
           (log= m 17)))

(defthmd leap-rewrite
  (implies (natp y)
           (equal (leap y)
	          (leap-guts (mod y 19))))
  :hints (("Goal" :in-theory (enable leap leap-guts))))

(defthmd mod-y-1
  (implies (posp y)
           (equal (mod (1- y) 19)
	          (mod (1- (mod y 19)) 19)))
  :hints (("Goal" :use ((:instance mod-sum (a -1) (b y) (n 19))))))

(defthmd mod-y+1
  (implies (posp y)
           (equal (mod (1+ y) 19)
	          (mod (1+ (mod y 19)) 19)))
  :hints (("Goal" :use ((:instance mod-sum (a 1) (b y) (n 19))))))

;; Thus, years y and yt have the same length under the following conditions:

(defthmd yearlength-equal-lemma
  (let ((dm (dmolad y))
        (dmt (dmolad yt))
        (dm+ (dmolad (1+ y)))
        (dmt+ (dmolad (1+ yt))))
    (implies (and (posp y)
                  (posp yt)
	  	  (= (mod y 19) (mod yt 19))
		  (= (mod (day dm) 7) (mod (day dmt) 7))
		  (= (hour dm) (hour dmt))
		  (= (part dm) (part dmt))
		  (= (mod (day dm+) 7) (mod (day dmt+) 7))
		  (= (hour dm+) (hour dmt+))
		  (= (part dm+) (part dmt+))
		  (= (- (day dm+) (day dm)) (- (day dmt+) (day dmt))))
             (equal (yearlength y) (yearlength yt))))
  :hints (("Goal" :in-theory (e/d (momentp yearlength rh-rewrite leap-rewrite) (acl2::mod-sums-cancel-1))
                  :use (mod-y-1 mod-y+1 momentp-dmolad
		        (:instance mod-y-1 (y yt))
		        (:instance mod-y+1 (y yt))
			(:instance momentp-dmolad (y yt))
			(:instance momentp-dmolad (y (1+ y)))
			(:instance momentp-dmolad (y (1+ yt)))))))

;; Next we show that 2 years that differ by 689472 satisfy those conditions.  This depends on the
;; observation that the number of months in any interval of 19 years is 235:

(defthmd monthsinyear-mod
  (implies (and (natp y) (natp k))
           (equal (monthsinyear (+ k (mod y 19)))
	          (monthsinyear (+ k y))))
  :hints (("Goal" :in-theory (e/d (monthsinyear leap) (ACL2::MOD-SUMS-CANCEL-1))
                  :use ((:instance mod-sum (a k) (b y) (n 19))))))

(defthmd monthsinyear-sum-mod
  (implies (and (natp y) (< y 19))
	   (equal (+ (monthsinyear y) (monthsinyear (+ y 1)) (monthsinyear (+ y 2))
	             (monthsinyear (+ y 3)) (monthsinyear (+ y 4)) (monthsinyear (+ y 5))
		     (monthsinyear (+ y 6)) (monthsinyear (+ y 7)) (monthsinyear (+ y 8))
		     (monthsinyear (+ y 9)) (monthsinyear (+ y 10)) (monthsinyear (+ y 11))
	             (monthsinyear (+ y 12)) (monthsinyear (+ y 13)) (monthsinyear (+ y 14))
	             (monthsinyear (+ y 15)) (monthsinyear (+ y 16)) (monthsinyear (+ y 17))
	             (monthsinyear (+ y 18)))
		  235))
  :hints (("Goal" :in-theory (enable bvecp)
                  :use ((:instance bvecp-member (x y) (n 5))))))

(defthmd monthsinyear-sum
  (implies (natp y)
	   (equal (+ (monthsinyear y) (monthsinyear (+ y 1)) (monthsinyear (+ y 2))
	             (monthsinyear (+ y 3)) (monthsinyear (+ y 4)) (monthsinyear (+ y 5))
	             (monthsinyear (+ y 6)) (monthsinyear (+ y 7)) (monthsinyear (+ y 8))
	             (monthsinyear (+ y 9)) (monthsinyear (+ y 10)) (monthsinyear (+ y 11))
	             (monthsinyear (+ y 12)) (monthsinyear (+ y 13)) (monthsinyear (+ y 14))
	             (monthsinyear (+ y 15)) (monthsinyear (+ y 16)) (monthsinyear (+ y 17))
	             (monthsinyear (+ y 18)))
		  235))
  :hints (("Goal" :in-theory (enable monthsinyear-mod)
                  :use ((:instance monthsinyear-mod (k 0))
		        (:instance monthsinyear-sum-mod (y (mod y 19)))))))

;; Therefore, two delayed moladot separated by a Metonic cycle differ by 235 lunations:

(defthmd dmolad+19
  (implies (posp y)
           (equal (expand (dmolad (+ y 19)))
	          (+ (expand (dmolad y))
		     (* 235 (expand (lunation))))))
  :hints (("Goal" :use (monthsinyear-sum expand-dmolad-next
                        (:instance expand-dmolad-next (y (+ y 1))) (:instance expand-dmolad-next (y (+ y 2)))
                        (:instance expand-dmolad-next (y (+ y 3))) (:instance expand-dmolad-next (y (+ y 4)))
                        (:instance expand-dmolad-next (y (+ y 5))) (:instance expand-dmolad-next (y (+ y 6)))
                        (:instance expand-dmolad-next (y (+ y 7))) (:instance expand-dmolad-next (y (+ y 8)))
                        (:instance expand-dmolad-next (y (+ y 9))) (:instance expand-dmolad-next (y (+ y 10)))
                        (:instance expand-dmolad-next (y (+ y 11))) (:instance expand-dmolad-next (y (+ y 12)))
                        (:instance expand-dmolad-next (y (+ y 13))) (:instance expand-dmolad-next (y (+ y 14)))
                        (:instance expand-dmolad-next (y (+ y 15))) (:instance expand-dmolad-next (y (+ y 16)))
                        (:instance expand-dmolad-next (y (+ y 17))) (:instance expand-dmolad-next (y (+ y 18)))
                        (:instance expand-dmolad-next (y (+ y 19)))))))

;; As consequence of dmolad+19 and yearlength-equal-lemma, y + 689472 and y have the same length:

(defun natp-induct (n)
  (if (posp n)
      (+ n (natp-induct (1- n)))
    0))

(defthmd dmolad+19k
  (implies (and (posp y) (natp k))
           (equal (expand (dmolad (+ y (* 19 k))))
	          (+ (expand (dmolad y))
		     (* 235 k (expand (lunation))))))
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/1" :use ((:instance dmolad+19 (y (+ y (* 19 (1- k)))))))))

(defthmd expand-dmolad+25920k
  (implies (and (momentp dm)
                (momentp dmt)
		(natp k)
		(= (expand dmt) (+ (expand dm) (* 25920 k))))
	   (equal (as 'day (+ (day dm) k) (as 'hour (hour dm) (as 'part (part dm) ())))
	          dmt))
  :hints (("Goal" :in-theory (enable expand momentp)
                  :use ((:instance expand= (x (as 'day (+ (day dm) k) (as 'hour (hour dm) (as 'part (part dm) ())))) (y dmt))))))

(defthmd dmolad-compare
  (let ((dm (dmolad y))
        (dmt (dmolad (+ y 689472))))
    (implies (posp y)
             (and (equal (day dmt) (+ (day dm) (* 7 35975351)))
	          (equal (mod (day dmt) 7) (mod (day dm) 7))
	          (equal (hour dmt) (hour dm))
		  (equal (part dmt) (part dm)))))
  :hints (("Goal" :in-theory (enable momentp)
                  :use (momentp-dmolad
		        (:instance momentp-dmolad (y (+ y 689472)))
		        (:instance expand-dmolad+25920k (dmt (dmolad (+ y 689472))) (dm (dmolad y)) (k 251827457))
		        (:instance dmolad+19k (k (/ 689472 19)))
			(:instance mod-mult (m (day (dmolad y))) (a 35975351) (n 7))))))

(defthmd yearlength-equal
  (implies (posp y)
           (equal (yearlength (+ y 689472))
	          (yearlength y)))
  :hints (("Goal" :in-theory (enable momentp)
                  :use (dmolad-compare
                        (:instance dmolad-compare (y (1+ y)))
                        (:instance yearlength-equal-lemma (yt (+ y 689472)))))))

;; It follows that the length of every year is equal to that of some year in the interval [1, 689472]:

(defthmd yearlength-equal-mul
  (implies (and (posp y) (natp k))
           (equal (yearlength (+ y (* k 689472)))
	          (yearlength y)))
  :hints (("Goal" :induct (natp-induct k))
          ("Subgoal *1/1" :use ((:instance yearlength-equal (y (+ y (* (1- k) 689472))))))))

(defthmd yearlength-equal-mod
  (implies (posp y)
           (equal (yearlength y)
	          (if (integerp (/ y 689472))
		      (yearlength 689472)
		    (yearlength (mod y 689472)))))
  :hints (("Goal" :use ((:instance mod-def (x y) (y 689472))
                        (:instance yearlength-equal-mul (y (mod y 689472)) (k (fl (/ y 689472))))
                        (:instance yearlength-equal-mul (y 689472) (k (1- (/ y 689472))))))))

;; We prove by exhaustive computation that the length of each year in the interval [1, 689472] is admissible.
;; Using the function rh-delay, this is achieved by a single execution of the computation indicated by
;; dmolad-next for each y in the interval:

(defund check-rh (i dm)
  (let ((dm+ (addtime dm (multime (monthsinyear i) (lunation)))))
    (member (- (+ (day dm+) (rh-delay (mod (day dm+) 7) (hour dm+) (part dm+) (leap (1+ i)) (leap i)))
	       (+ (day dm) (rh-delay (mod (day dm) 7) (hour dm) (part dm) (leap i) (leap (- i 1)))))
            (if1 (leap i)
	         '(383 384 385)
	       '(353 354 355)))))

(defthmd check-yearlength
  (implies (posp y)
           (iff (check-rh y (dmolad y))
	        (member (yearlength y)
                        (if1 (leap y)
	                     '(383 384 385)
	                   '(353 354 355)))))
  :hints (("Goal" :in-theory (enable yearlength rh-rewrite check-rh)
                  :use (dmolad-next))))

(defun check-all (i y dm)
  (declare (xargs :measure (nfix (- y i))))
  (if (and (posp i) (posp y) (< i y))
      (and (check-rh i dm)
	   (check-all (1+ i) y (addtime dm (multime (monthsinyear i) (lunation)))))
    t))

(defthmd check-all-lemma
  (implies (and (posp i) (posp k) (posp y) (<= i k) (< k y)
                (check-all i y (dmolad i)))
	   (check-rh k (dmolad k)))
  :hints (("Subgoal *1/4" :use ((:instance dmolad-next (y i))))))

;; We won't check the following explicitly.  The computation is done in the course of the proof of
;; check-small-yearlength, which takes about 4 seconds:

;; (check-all 1 689473 (beharad))

;; Added by Matt K. to avoid stack overflow in Allegro CL (and perhaps other
;; Lisps that don't compile on-the-fly):
(comp t)

(defthmd check-small-yearlength
  (implies (and (posp y) (<= y 689472))
           (member (yearlength y)
                   (if1 (leap y)
	                '(383 384 385)
	              '(353 354 355))))
  :hints (("Goal" :in-theory (enable check-yearlength)
                  :use ((:instance check-all-lemma (i 1) (k y) (y 689473))))))

;; The desired result follows:

(defthmd legal-year-lengths
  (implies (posp y)
           (member (yearlength y)
                   (if1 (leap y)
	                '(383 384 385)
	              '(353 354 355))))
  :hints (("Goal" :in-theory (enable leap-rewrite)
                  :use (yearlength-equal-mod
                        (:instance check-small-yearlength (y 689472))
			(:instance check-small-yearlength (y (mod y 689472)))
			(:instance mod-of-mod (x y) (k 36288) (n 19))
			(:instance mod-0-int (m y) (n 19))))))


;;-----------------------------------------------------------------------------------------------------------
;; Admissibility of year lengths: second proof
;;-----------------------------------------------------------------------------------------------------------

;; Complement of a time of day:

(defund comp-time (hour part)
  (if (zp part)
      (mv (- 24 hour) 0)
    (mv (- 23 hour) (- 1080 part))))

;; Number of days between one delayed molad and the next:

(defthm next-molad
  (implies (and (momentp molad)
		(momentp delta))
           (let ((next (addtime molad delta)))
	     (mv-let (comp-hour comp-part) (comp-time (hour delta) (part delta))
	       (if1 (earlier molad comp-hour comp-part)
	            (and (= (day next) (+ (day molad) (day delta)))
		         (= (earlier next (hour delta) (part delta)) 0))
	         (and (= (day next) (+ 1 (day molad) (day delta)))
		      (= (earlier next (hour delta) (part delta)) 1))))))
  :hints (("Goal" :nonlinearp t
                  :in-theory (enable addtime momentp comp-time expand earlier)
		  :use ((:instance expand+ (x molad) (y delta))
		        (:instance momentp+ (x molad) (y delta))))))

(defthmd next-molad-common
  (implies (and (posp y) (= (common y) 1))
           (let ((molad (dmolad y))
	         (next (dmolad (1+ y))))
	     (if1 (earlier molad 15 204)
                  (and (= (day next) (+ (day molad) 354))
		       (= (earlier next 8 876) 0))
	        (and (= (day next) (+ (day molad) 355))
		     (= (earlier next 8 876) 1)))))
  :hints (("Goal" :in-theory (enable common earlier monthsinyear momentp lunation)
                  :use (momentp-dmolad dmolad-next
		        (:instance next-molad (molad (dmolad y)) (delta (multime 12 (lunation))))))))

(defthm next-molad-leap
  (implies (and (posp y) (= (leap y) 1))
           (let ((molad (dmolad y))
	         (next (dmolad (1+ y))))
	     (if1 (earlier molad 2 491)
                  (and (= (day next) (+ (day molad) 383))
		       (= (earlier next 21 589) 0))
	        (and (= (day next) (+ (day molad) 384))
		     (= (earlier next 21 589) 1)))))
  :hints (("Goal" :in-theory (enable common earlier monthsinyear momentp lunation)
                  :use (momentp-dmolad dmolad-next
		        (:instance next-molad (molad (dmolad y)) (delta (multime 13 (lunation))))))))

;; The day of the week that occurs k days after a given day of the week:

(defthmd dayofweek-plus
  (implies (and (natp d) (natp k))
           (equal (dayofweek (+ k d))
	          (dayofweek (+ k (dayofweek d)))))
  :hints (("Goal" :in-theory (enable dayofweek))))

;; Enumeration of the days of the week (used to force a case split in the main result):

(defthmd days-of-week
  (implies (natp d)
           (member (dayofweek d)
	           '(0 1 2 3 4 5 6)))
  :hints (("Goal" :in-theory (enable dayofweek))))

;; The following is proved by a case analysis based on next-molad-common and next-molad-leap:

(defthm legal-year-lengths-alt
  (implies (posp y)
           (member (yearlength y)
		   (if1 (leap y)
		        '(383 384 385)
		      '(353 354 355))))
  :hints (("Goal" :in-theory (enable common momentp yearlength earlier)
                  :expand ((roshhashanah y) (roshhashanah (+ 1 y)))
                  :use (momentp-dmolad next-molad-common next-molad-leap
			(:instance momentp-dmolad (y (1+ y)))
			(:instance dayofweek-plus (d (day (dmolad y))) (k (if1 (leap y) 383 354)))
			(:instance dayofweek-plus (d (day (dmolad y))) (k (if1 (leap y) 384 355)))
			(:instance days-of-week (d (day (dmolad y))))))))


;;-----------------------------------------------------------------------------------------------------------
;; Only 20 keviyot (combinations of year length and day of the week of Rosh Hashanah) are possible.
;;-----------------------------------------------------------------------------------------------------------

(defthmd dayofweek-roshhashanah
  (implies (posp y)
           (member (dayofweek (roshhashanah y))
	           '(0 2 3 5)))
  :hints (("Goal" :in-theory (enable dayofweek-plus momentp common roshhashanah)
	   :use (momentp-dmolad (:instance days-of-week (d (day (dmolad y))))))))

(defthmd keviyot
  (implies (posp y)
           (let ((dw (dayofweek (roshhashanah y)))
	         (len (yearlength y)))
	     (or (and (= dw 3)
	              (member len '(354 384)))
		 (and (member dw '(0 2))
		      (member len '(353 355 383 385)))
		 (and (= dw 5)
		      (member len '(354 355 383 385))))))
  :hints (("Goal" :in-theory (enable momentp roshhashanah dayofweek-plus common yearlength)
                  :use (legal-year-lengths-alt dayofweek-roshhashanah momentp-dmolad next-molad-leap
					   (:instance dayofweek-roshhashanah (y (1+ y)))))))


;;-----------------------------------------------------------------------------------------------------------
;; Landau's theorem: The molad of every month occurs before the end of the 1st day of the month.
;;-----------------------------------------------------------------------------------------------------------

(defthm natp-roshhashanah
  (implies (natp y) (natp (roshhashanah y)))
  :hints (("Goal" :in-theory (enable momentp roshhashanah)
                  :use (momentp-dmolad)))
  :rule-classes (:rewrite :type-prescription))

;; This bound is sufficient for year lengths 355, 384, and 385:

(defthmd molad-roshhashanah
  (implies (natp y)
            (< (expand (molad y))
	       (* 1080 (+ 18 (* 24 (roshhashanah y))))))
  :hints (("Goal" :in-theory (enable earlier addtime momentp expand roshhashanah dmolad)
		  :nonlinearp t
		  :cases ((= (earlier (molad y) 18 0) 0))
                  :use (momentp-molad
		        (:instance fl-unique (x (/ (part (molad y)) 1080)) (n 0))
		        (:instance fl-unique (x (/ (+ (hour (molad y)) 6) 24)) (n 1))
		        (:instance fl-unique (x (/ (+ (hour (molad y)) 6) 24)) (n 0))))))

;; This bound is required for year lengths 353, 354, and 383:

(defthmd molad-roshhashanah-next
  (implies (posp y)
            (< (expand (molad y))
	       (- (* 1080 (+ 18 (* 24 (+ (roshhashanah y) (yearlength y)))))
		  (* (if1 (leap y) 13 12) (expand (lunation))))))
  :hints (("Goal" :in-theory (enable monthsinyear common momentp expand yearlength)
                  :use (momentp-molad molad-next
		        (:instance expand+ (x (molad y)) (y (multime (if1 (common y) 12 13) (lunation))))
			(:instance molad-roshhashanah (y (1+ y)))))))

;; First day of month:

(defun firstofmonth (month y) (as 'day 1 (as 'month month (as 'year y ()))))

;; This splits into the 6 cases of year length and applies one of the above 2 bounds in each case:

(defthmd expand-monthlymolad
  (implies (and (posp y)
                (posp month)
		(<= month (if1 (leap y) 13 12)))
	   (< (expand (monthlymolad month y))
	      (* 1080 24 (1+ (h2a (firstofmonth month y))))))
  :hints (("Goal" :in-theory (enable monthlymolad monthlength h2a expand+ expand*)
                  :use (legal-year-lengths-alt molad-roshhashanah molad-roshhashanah-next)
	          :expand ((:free (x y z) (h2a-loop-0 x y z))))))

(defthmd expand-day
  (implies (and (momentp x)
                (natp d)
		(< (expand x) (* 1080 24 (1+ d))))
	   (<= (day x) d))
  :hints (("Goal" :in-theory (enable momentp expand))))

(defthmd natp-h2a
  (implies (and (posp (ag 'year date))
                (posp (ag 'day date))
                (posp (ag 'month date))
		(<= (ag 'month date) 13))
           (natp (h2a date)))
  :hints (("Goal" :in-theory (enable monthlength h2a h2a-loop-0)
	          :expand ((:free (x y z) (h2a-loop-0 x y z))))))

(defthm landau-thm
  (implies (and (posp y)
		(posp month)
		(<= month (monthsinyear y)))
	   (<= (day (monthlymolad month y))
	       (h2a (firstofmonth month y))))
  :hints (("Goal" :in-theory (enable monthsinyear monthlymolad)
                  :use (expand-monthlymolad
		        (:instance natp-h2a (date (firstofmonth month y)))
                        (:instance expand-day (x (monthlymolad month y))
				              (d (h2a (firstofmonth month y))))))))



