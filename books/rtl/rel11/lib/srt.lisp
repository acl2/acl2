; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
;
; Contact:
;   David M. Russinoff
;   1106 W 9th St., Austin, TX 78703
;   david@russinoff.com
;   http://www.russinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(include-book "defs")

;;**********************************************************************************
;; SRT Division
;;**********************************************************************************

(defsection-rtl |SRT Division and Quotient Digit Selection|
  |SRT Division and Square Root|

(encapsulate (((e$) => *) ((d$) => *) ((x$) => *) ((a$) => *) ((q$ *) => *))
  (local (defun e$ () 2))
  (local (defun d$ () 1/2))
  (local (defun x$ () 1/2))
  (local (defun a$ () 2))
  (local (defun q$ (j) (declare (ignore j)) 0))
  (defund r$ () (expt 2 (e$)))
  (defund rho$ () (/ (a$) (1- (r$))))
  (defthmd e$-constraint
    (not (zp (e$))))
  (defthmd d$-constraint
    (and (rationalp (d$))
         (> (d$) 0)))
  (defthmd x$-constraint
    (and (rationalp (x$))
	 (> (x$) 0)
         (< (x$) (* 2 (d$)))))
  (defthmd a$-constraint
    (not (zp (a$))))
  (defthm q$-constraint
    (implies (not (zp j))
             (and (integerp (q$ j))
                  (<= (abs (q$ j)) (a$))))
    :rule-classes
    ((:type-prescription
      :corollary
      (implies (not (zp j))
               (integerp (q$ j))))
     (:linear
      :corollary
      (implies (not (zp j))
               (and (<= (- (a$)) (q$ j))
                    (<= (q$ j) (a$)))))))
  (defthmd rho$-constraint
    (and (< 1/2 (rho$))
         (<= (rho$) 1))))

(defund quot$ (j)
  (if (zp j)
      0
    (+ (quot$ (1- j))
       (* (q$ j) (expt (r$) (- 1 j))))))

(defund rem$ (j)
  (* (expt (r$) (1- j))
     (- (x$) (* (d$) (quot$ j)))))

(defthmd rem0-div-rewrite
  (equal (rem$ 0) (/ (x$) (r$))))

(defthmd rem-div-recurrence
  (implies (natp j)
           (equal (rem$ (+ 1 j))
                  (- (* (r$) (rem$ j))
                     (* (q$ (1+ j)) (d$))))))

(defthmd rem0-div-bound
  (< (abs (rem$ 0)) (* (rho$) (d$))))

(defund sel-upper-div (k d) (* (+ k (rho$)) d))

(defund sel-lower-div (k d) (* (- k (rho$)) d))

(defthmd rem-div-bnd-next
  (implies (and (natp j)
                (<= (sel-lower-div (q$ (1+ j)) (d$)) (* (r$) (rem$ j)))
                (>= (sel-upper-div (q$ (1+ j)) (d$)) (* (r$) (rem$ j))))
           (<= (abs (rem$ (1+ j))) (* (rho$) (d$)))))

(defthm select-overlap
  (implies (integerp k)
           (and (< (sel-lower-div k (d$)) (sel-lower-div (1+ k) (d$)))
                (< (sel-lower-div (1+ k) (d$)) (sel-upper-div k (d$)))
                (< (sel-upper-div k (d$)) (sel-upper-div (1+ k) (d$)))
		(<= (sel-upper-div k (d$)) (sel-lower-div (+ k 2) (d$))))))

(defthmd div-containment
  (and (equal (sel-upper-div (a$) (d$)) (* (r$) (rho$) (d$)))
       (equal (sel-lower-div (- (a$)) (d$)) (- (* (r$) (rho$)(d$))))))

;;------------------------------------------------------------------------------------------------------------------
;; Minimally Redundant Radix-4 Division
;;------------------------------------------------------------------------------------------------------------------

(defun md4 (k)
  (case k (2 13/8) (1 4/8) (0 -3/8) (-1 -12/8)))

(defund select-digit-d4 (a)
  (cond ((<= (md4 2) a) 2)
        ((<= (md4 1) a) 1)
        ((<= (md4 0) a) 0)
        ((<= (md4 -1) a) -1)
        (t -2)))

(defthmd sel-limits-4
  (implies (and (<= 63/64 (d$))
                (<= (d$) 9/8)
                (= (r$) 4)
		(= (a$) 2)
                (member k '(-2 -1 0 1 2)))
           (and (<= (sel-lower-div k (d$))
                    (max (sel-lower-div k 63/64)
                         (sel-lower-div k 9/8)))
                (>= (sel-upper-div k (d$))
                    (min (sel-upper-div k 63/64)
                         (sel-upper-div k 9/8))))))

(defthmd sel-limits-check-4
  (implies (and (<= 63/64 (d$))
                (<= (d$) 9/8)
                (= (r$) 4)
		(= (a$) 2)
                (member k '(-1 0 1 2)))
           (and (<= (+ (max (sel-lower-div k 63/64) (sel-lower-div k 9/8)) 1/8)
                    (md4 k))
                (>= (min (sel-upper-div k 63/64) (sel-upper-div k 9/8))
                    (md4 k)))))

(defthmd md4-k-bounds
  (implies (and (<= 63/64 (d$))
                (<= (d$) 9/8)
                (= (r$) 4)
		(= (a$) 2))
           (and (implies (member k '(-1 0 1 2))
                         (<= (+ (sel-lower-div k (d$)) 1/8)
                             (md4 k)))
                (implies (member k '(-2 -1 0 1))
                         (>= (sel-upper-div k (d$))
                             (md4 (1+ k)))))))

(defthmd srt-div-rad-4
  (implies (and (= (r$) 4)
                (= (a$) 2)
                (<= 63/64 (d$))
                (<= (d$) 9/8)
                (natp j)
                (<= (abs (rem$ j)) (* 2/3 (d$)))
                (rationalp approx)
                (integerp (* 8 approx))
                (< (abs (- approx (* 4 (rem$ j)))) 1/8)
                (= (q$ (1+ j)) (select-digit-d4 approx)))
	   (<= (abs (rem$ (1+ j))) (* 2/3 (d$)))))

;;------------------------------------------------------------------------------------------------------------------
;; Minimally Redundant Radix-8 Division
;;------------------------------------------------------------------------------------------------------------------

(defun md8*64 (k i)
  (case (fl (/ i 2))
    (0 (case k (4 (if (= i 0) 113 115)) (3 82) (2 50) (1 16) (0 -16) (-1 -48) (-2 -81) (-3 (if (= i 0) -112 -114))))
    (1 (case k (4 (if (= i 2) 117 118)) (3 84) (2 50) (1 16) (0 -16) (-1 -50) (-2 -83) (-3 (if (= i 2) -116 -117))))
    (2 (case k (4 121) (3 86) (2 52) (1 16) (0 -16) (-1 -52) (-2 -86) (-3 -120)))
    (3 (case k (4 125) (3 90) (2 54) (1 18) (0 -18) (-1 -54) (-2 -88) (-3 -124)))
    (4 (case k (4 128) (3 92) (2 54) (1 18) (0 -18) (-1 -54) (-2 -90) (-3 -127)))
    (5 (case k (4 132) (3 94) (2 56) (1 18) (0 -18) (-1 -56) (-2 -94) (-3 -131)))
    (6 (case k (4 135) (3 96) (2 58) (1 18) (0 -18) (-1 -58) (-2 -96) (-3 -134)))
    (7 (case k (4 139) (3 100) (2 60) (1 20) (0 -20) (-1 -60) (-2 -98) (-3 -138)))
    (8 (case k (4 142) (3 102) (2 60) (1 20) (0 -20) (-1 -60) (-2 -100) (-3 -141)))
    (9 (case k (4 146) (3 104) (2 62) (1 20) (0 -20) (-1 -62) (-2 -104) (-3 -144)))
    (10 (case k (4 150) (3 106) (2 64) (1 20) (0 -20) (-1 -64) (-2 -106) (-3 -148)))
    (11 (case k (4 152) (3 108) (2 64) (1 20) (0 -20) (-1 -64) (-2 -108) (-3 -152)))
    (12 (case k (4 156) (3 112) (2 66) (1 22) (0 -22) (-1 -66) (-2 -112) (-3 -156)))
    (13 (case k (4 160) (3 114) (2 68) (1 22) (0 -22) (-1 -68) (-2 -114) (-3 -158)))
    (14 (case k (4 164) (3 116) (2 70) (1 24) (0 -24) (-1 -70) (-2 -116) (-3 -162)))
    (15 (case k (4 166) (3 118) (2 70) (1 24) (0 -24) (-1 -70) (-2 -118) (-3 -166)))
    (16 (case k (4 170) (3 120) (2 72) (1 24) (0 -24) (-1 -72) (-2 -120) (-3 -170)))
    (17 (case k (4 173) (3 124) (2 73) (1 24) (0 -24) (-1 -72) (-2 -124) (-3 -172)))
    (18 (case k (4 176) (3 126) (2 76) (1 24) (0 -24) (-1 -76) (-2 -124) (-3 -176)))
    (19 (case k (4 180) (3 128) (2 76) (1 24) (0 -24) (-1 -76) (-2 -128) (-3 -180)))
    (20 (case k (4 184) (3 132) (2 78) (1 24) (0 -24) (-1 -78) (-2 -132) (-3 -184)))
    (21 (case k (4 188) (3 134) (2 80) (1 28) (0 -28) (-1 -80) (-2 -134) (-3 -188)))
    (22 (case k (4 190) (3 136) (2 82) (1 28) (0 -28) (-1 -82) (-2 -136) (-3 -190)))
    (23 (case k (4 194) (3 138) (2 82) (1 28) (0 -28) (-1 -82) (-2 -138) (-3 -194)))
    (24 (case k (4 198) (3 140) (2 84) (1 28) (0 -28) (-1 -84) (-2 -140) (-3 -198)))
    (25 (case k (4 200) (3 142) (2 84) (1 28) (0 -28) (-1 -84) (-2 -142) (-3 -200)))
    (26 (case k (4 204) (3 146) (2 86) (1 28) (0 -28) (-1 -86) (-2 -146) (-3 -204)))
    (27 (case k (4 208) (3 148) (2 88) (1 28) (0 -28) (-1 -88) (-2 -148) (-3 -208)))
    (28 (case k (4 212) (3 152) (2 90) (1 28) (0 -28) (-1 -90) (-2 -152) (-3 -212)))
    (29 (case k (4 214) (3 152) (2 90) (1 28) (0 -28) (-1 -90) (-2 -152) (-3 -214)))
    (30 (case k (4 218) (3 154) (2 94) (1 28) (0 -28) (-1 -94) (-2 -154) (-3 -218)))
    (31 (case k (4 222) (3 158) (2 94) (1 32) (0 -32) (-1 -94) (-2 -158) (-3 -222)))))

(defund md8 (k i)
  (/ (md8*64 k i) 64))

(defund max-lower (i k)
  (max (sel-lower-div k (+ 1/2 (/ i 128)))
       (sel-lower-div k (+ 1/2 (/ (1+ i) 128)))))

(defund min-upper (i k)
  (min (sel-upper-div k (+ 1/2 (/ i 128)))
       (sel-upper-div k (+ 1/2 (/ (1+ i) 128)))))

(defthmd sel-limits-check-8
  (implies (and (= (r$) 8)
                (= (a$) 4)
                (bvecp i 6)
                (member k '(-3 -2 -1 0 1 2 3 4)))
           (and (<= (+ (max-lower i k) 1/64)
                    (md8 k i))
                (>= (min-upper i (1- k))
                    (md8 k i)))))

(defund i64 (d) (fl (* 128 (- d 1/2))))

(defthmd sel-limits-8
  (implies (and (= (r$) 8)
                (= (a$) 4)
                (<= 1/2 (d$))
		(< (d$) 1)
                (member k '(-4 -3 -2 -1 0 1 2 3 4)))
           (and (<= (sel-lower-div k (d$))
                    (max-lower (i64 (d$)) k))
                (>= (sel-upper-div k (d$))
                    (min-upper (i64 (d$)) k)))))

(defthmd md8-k-bounds
  (implies (and (= (r$) 8)
                (= (a$) 4)
                (<= 1/2 (d$))
		(< (d$) 1))
           (and (implies (member k '(-3 -2 -1 0 1 2 3 4))
                         (<= (+ (sel-lower-div k (d$)) 1/64)
                             (md8 k (i64 (d$)))))
                (implies (member k '(-4 -3 -2 -1 0 1 2 3))
                         (>= (sel-upper-div k (d$))
                             (md8 (1+ k) (i64 (d$))))))))

(defund select-digit-d8 (a i)
  (cond ((<= (md8 4 i) a) 4)
        ((<= (md8 3 i) a) 3)
        ((<= (md8 2 i) a) 2)
        ((<= (md8 1 i) a) 1)
        ((<= (md8 0 i) a) 0)
        ((<= (md8 -1 i) a) -1)
        ((<= (md8 -2 i) a) -2)
        ((<= (md8 -3 i) a) -3)
        (t -4)))

(defthmd srt-div-rad-8
  (implies (and (= (r$) 8)
                (= (a$) 4)
                (<= 1/2 (d$))
		(< (d$) 1)
                (natp j)
                (<= (abs (rem$ j)) (* 4/7 (d$)))
                (rationalp approx)
                (integerp (* 64 approx))
                (< (abs (- approx (* 8 (rem$ j)))) 1/64)
                (= (q$ (1+ j)) (select-digit-d8 approx (i64 (d$)))))
	   (<= (abs (rem$ (1+ j))) (* 4/7 (d$)))))

)

;;**********************************************************************************
;; SRT Square Root Extraction
;;**********************************************************************************

(defsection-rtl |SRT Square Root Extraction| |SRT Division and Square Root|

(encapsulate (((e%) => *) ((x%) => *) ((a%) => *) ((q% *) => *))
  (local (defun e% () 2))
  (local (defun x% () 1/2))
  (local (defun a% () 2))
  (local (defun q% (j) (declare (ignore j)) 0))
  (defund r% () (expt 2 (e%)))
  (defund rho% () (/ (a%) (1- (r%))))
  (defthmd e%-constraint
    (not (zp (e%))))
  (defthmd x%-constraint
    (and (rationalp (x%))
         (<= 1/4 (x%))
         (< (x%) 1)))
  (defthmd a%-constraint
    (not (zp (a%))))
  (defthm q%-constraint
    (implies (not (zp j))
             (and (integerp (q% j))
                  (<= (abs (q% j)) (a%))))
    :rule-classes
    ((:type-prescription
      :corollary
      (implies (not (zp j))
               (integerp (q% j))))
     (:linear
      :corollary
      (implies (not (zp j))
               (and (<= (- (a%)) (q% j))
                    (<= (q% j) (a%)))))))
  (defthmd rho%-constraint
    (and (< 1/2 (rho%))
         (<= (rho%) 1))))

(defund quot% (j)
  (if (zp j)
      1
    (+ (quot% (1- j))
       (* (q% j) (expt (r%) (- j))))))

(defund rem% (j)
  (* (expt (r%) j)
     (- (x%) (* (quot% j) (quot% j)))))

(defthmd int-quot-sqrt
  (implies (natp j)
           (integerp (* (expt (r%) j) (quot% j)))))

(defthmd rem0-sqrt-rewrite
  (equal (rem% 0) (1- (x%))))

(defthmd rem-sqrt-recurrence
  (implies (natp j)
           (equal (rem% (+ 1 j))
                  (- (* (r%) (rem% j))
                     (* (q% (1+ j))
		        (+ (* 2 (quot% j))
			   (* (expt (r%) (- (1+ j)))
			      (q% (1+ j)))))))))

(defund blo% (j)
  (+ (* -2 (rho%) (quot% j))
     (* (rho%) (rho%) (expt (r%) (- j)))))

(defund bhi% (j)
  (+ (* 2 (rho%) (quot% j))
     (* (rho%) (rho%) (expt (r%) (- j)))))

(defthm blohi
  (implies (natp j)
           (iff (and (<= (expt (- (quot% j) (* (rho%) (expt (r%) (- j)))) 2)
                         (x%))
                     (>= (expt (+ (quot% j) (* (rho%) (expt (r%) (- j)))) 2)
                         (x%)))
                (and (<= (blo% j) (rem% j))
		     (>= (bhi% j) (rem% j)))))
  :rule-classes ())

(defthmd rem0-sqrt-bounds
  (and (<= (blo% 0) (rem% 0))
       (>= (bhi% 0) (rem% 0))))

(defund sel-upper-sqrt (k j)
  (+ (* 2 (+ k (rho%)) (quot%  j))
     (* (+ k (rho%)) (+ k (rho%)) (expt (r%) (- (1+ j))))))

(defund sel-lower-sqrt (k j)
  (+ (* 2 (- k (rho%)) (quot%  j))
     (* (- k (rho%)) (- k (rho%)) (expt (r%) (- (1+ j))))))

(defthm rem-sqrt-bnds-next
  (implies (and (natp j)
                (<= (sel-lower-sqrt (q% (1+ j)) j)
		    (* (r%) (rem% j)))
                (>= (sel-upper-sqrt (q% (1+ j)) j)
		    (* (r%) (rem% j))))
	   (and (<= (blo% (1+ j))
	            (rem% (1+ j)))
		(>= (bhi% (1+ j))
	            (rem% (1+ j)))))
  :rule-classes ())

(defthmd sqrt-containment
  (implies (natp j)
           (and (equal (sel-upper-sqrt (a%) j) (* (r%) (bhi% j)))
                (equal (sel-lower-sqrt (- (a%)) j) (* (r%) (blo% j))))))

;;------------------------------------------------------------------------------------------------------------------
;; Minimally Redundant Radix-4 Square Root
;;------------------------------------------------------------------------------------------------------------------

(defun ms4*8 (i j k)
  (case i
    (0 (case k
         (2 12)
         (1 4)
         (0 -4)
         (-1 (if (= j 1) -11 -12))))
    (1 (case k
         (2 (if (= j 2) 15 13))
         (1 4)
         (0 -4)
         (-1 -13)))
    (2 (case k
         (2 15)
         (1 4)
         (0 -4)
         (-1 -15)))
    (3 (case k
         (2 16)
         (1 6)
         (0 -6)
         (-1 -16)))
    (4 (case k
         (2 18)
         (1 6)
         (0 -6)
         (-1 -18)))
    (5 (case k
         (2 20)
         (1 8)
         (0 -6)
         (-1 -20)))
    (6 (case k
         (2 20)
         (1 8)
         (0 -8)
         (-1 -20)))
    (7 (case k
         (2 22)
         (1 8)
         (0 -8)
         (-1 -22)))
    (8 (case k
         (2 24)
         (1 8)
         (0 -8)
         (-1 (if (= j 0) -20 -24))))))

(defund ms4 (i j k)
  (/ (ms4*8 i j k) 8))

(defund i% (j)
  (* 16 (- (quot% (min (nfix j) 2)) 1/2)))

(defund select-digit-s4 (a i j)
  (cond ((<= (ms4 i j 2) a) 2)
        ((<= (ms4 i j 1) a) 1)
        ((<= (ms4 i j 0) a) 0)
        ((<= (ms4 i j -1) a) -1)
        (t -2)))

(defund quot%-bnds-inv (j)
  (and (<= 1/2 (quot% j))
       (>= 1 (quot% j))))

(defund rem%-bnds-inv (j)
  (and (<= (blo% j) (rem% j))
       (>= (bhi% j) (rem% j))))

(encapsulate (((approx% *) => *))
  (local (defun approx% (j) (* 4 (rem% j))))
  (defthm ratp-approx%
    (rationalp (approx% j))
    :rule-classes (:type-prescription :rewrite)))

(defund approx%-bounds (j k)
  (and (implies (< (approx% j) (ms4 (i% j) j k))
                (< (* 4 (rem% j)) (ms4 (i% j) j k)))
       (implies (>= (approx% j) (ms4 (i% j) j k))
                (> (* 4 (rem% j)) (- (ms4 (i% j) j k) 1/32)))))

(defund approx%-inv (j)
  (and (= (q% (1+ j)) (select-digit-s4 (approx% j) (i% j) j))
       (approx%-bounds j 2)
       (approx%-bounds j 1)
       (approx%-bounds j 0)
       (approx%-bounds j -1)))

(defund s4-inv (j)
  (and (quot%-bnds-inv j)
       (rem%-bnds-inv j)
       (approx%-inv j)))

(defund s4-hyp (j)
  (if (zp j)
      (s4-inv 0)
    (and (s4-inv j)
         (s4-hyp (1- j)))))

(defthmd srt-sqrt-rad-4
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j))
	   (and (quot%-bnds-inv (1+ j))
                (rem%-bnds-inv (1+ j)))))

;;------------------------------------------------------------------------------------------------------------------

(defun ms8-0 (k)
  (nth (- 1 k) '(0 -64 -176 -272 -352)))

(defun ms8-1 (i k)
  (nth (- 4 k) (nth (/ i 8) '((236 166 96 31 -32 -92 -152 -212)
                              (291 206 121 41 -42 -122 -192 -267)
                              (351 241 141 46 -47 -142 -232 -322)
                              (406 281 171 61 -62 -172 -277 -377)
                              (461 326 191 61 -62 -192 -317 -442)))))

(defun ms8-2 (i k)
  (nth (- 4 k) (nth i '((226 161 97 32 -32 -97 -161 -226)
                        (231 165 99 33 -33 -99 -165 -231)
                        (238 170 102 34 -34 -102 -170 -238)
                        (245 175 105 35 -35 -105 -175 -245)
                        (252 180 108 36 -36 -108 -180 -252)
                        (259 185 112 37 -37 -112 -185 -259)
                        (266 190 114 38 -38 -114 -190 -266)
                        (273 195 117 39 -39 -117 -195 -273)
                        (280 200 120 40 -40 -120 -200 -280)
                        (287 205 123 41 -41 -123 -205 -287)
                        (294 210 128 42 -42 -128 -210 -294)
                        (301 215 129 43 -43 -129 -215 -301)
                        (308 220 132 44 -44 -132 -220 -308)
                        (315 225 135 45 -45 -135 -225 -315)
                        (322 230 138 48 -48 -138 -230 -322)
                        (329 235 141 48 -48 -141 -235 -329)
                        (336 240 144 48 -48 -144 -240 -336)
                        (343 245 147 49 -49 -147 -245 -343)
                        (350 250 150 50 -50 -150 -250 -350)
                        (357 255 153 51 -51 -153 -255 -357)
                        (364 260 156 52 -52 -156 -260 -364)
                        (371 265 160 53 -53 -160 -265 -371)
                        (378 270 162 54 -54 -162 -270 -378)
                        (385 275 165 55 -55 -165 -275 -385)
                        (392 280 168 56 -56 -168 -280 -392)
                        (398 285 171 57 -57 -171 -285 -398)
                        (406 290 174 58 -58 -174 -290 -406)
                        (413 295 177 59 -59 -177 -295 -413)
                        (420 300 180 60 -60 -180 -300 -420)
                        (427 305 183 61 -61 -183 -305 -427)
                        (434 310 186 62 -62 -186 -310 -434)
                        (441 315 189 64 -64 -189 -315 -441)
                        (447 319 191 64 -64 -191 -319 -447)))))

(defun ms8*64 (i j k)
  (case j
    (0 (ms8-0 k))
    (1 (ms8-1 i k))
    (t (ms8-2 i k))))

(defund ms8 (i j k)
  (/ (ms8*64 i j k) 64))

(defund select-digit-s8 (a i j)
  (cond ((<= (ms8 i j 4) a) 4)
        ((<= (ms8 i j 3) a) 3)
        ((<= (ms8 i j 2) a) 2)
        ((<= (ms8 i j 1) a) 1)
        ((<= (ms8 i j 0) a) 0)
        ((<= (ms8 i j -1) a) -1)
        ((<= (ms8 i j -2) a) -2)
        ((<= (ms8 i j -3) a) -3)
        (t -4)))

(defund i8% (j)
  (* 64 (- (quot% (min (nfix j) 2)) 1/2)))

(defund quot%-bnds-inv (j)
  (and (<= 1/2 (quot% j))
       (>= 1 (quot% j))))

(defund rem%-bnds-inv (j)
  (and (<= (blo% j) (rem% j))
       (>= (bhi% j) (rem% j))))

(encapsulate (((approx8% *) => *))
  (local (defun approx8% (j) (* 8 (rem% j))))
  (defthm ratp-approx8%
    (rationalp (approx8% j))
    :rule-classes (:type-prescription :rewrite))
  (defthm approx8%-0
    (equal (approx8% 0) (* 8 (rem% 0)))))

(defund approx8%-bounds (j k)
  (and (implies (< (approx8% j) (ms8 (i8% j) j k))
                (< (* 8 (rem% j)) (ms8 (i8% j) j k)))
       (implies (>= (approx8% j) (ms8 (i8% j) j k))
                (> (* 8 (rem% j)) (- (ms8 (i8% j) j k) 1/128)))))

(defund approx8%-inv (j)
  (and (= (q% (1+ j)) (select-digit-s8 (approx8% j) (i8% j) j))
       (approx8%-bounds j 4)
       (approx8%-bounds j 3)
       (approx8%-bounds j 2)
       (approx8%-bounds j 1)
       (approx8%-bounds j 0)
       (approx8%-bounds j -1)
       (approx8%-bounds j -2)
       (approx8%-bounds j -3)))

(defund s8-inv (j)
  (and (quot%-bnds-inv j)
       (rem%-bnds-inv j)
       (approx8%-inv j)))

(defund s8-hyp (j)
  (if (zp j)
      (s8-inv 0)
    (and (s8-inv j)
         (s8-hyp (1- j)))))

(defthmd srt-sqrt-rad-8
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (natp j)
		(s8-hyp j))
	   (and (quot%-bnds-inv (1+ j))
                (rem%-bnds-inv (1+ j))))
  :hints (("Goal" :use (rem%-8-bnds quot8%-bnds))))

)
