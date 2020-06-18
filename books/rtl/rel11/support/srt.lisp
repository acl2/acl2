(in-package "RTL")

(include-book "basic")
(include-book "bits")
(include-book "float")

(local (include-book "arithmetic-5/top" :dir :system))

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-<
                    ash-to-floor |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)| ACL2::|(logior 1 x)|))

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
         ;(<= (d$) (x$))
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

(local-in-theory (disable (r$) (rho$)))

(local-defthm natp-e$
  (natp (e$))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (e$-constraint))))

(local-defthm ratp-x$
  (rationalp (x$))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (x$-constraint))))

(local-defthm ratp-d$
  (rationalp (d$))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (d$-constraint))))

(local-defthm intp-a$
  (integerp (a$))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (a$-constraint))))

(local-defthm intp-q$
  (implies (not (zp j))
           (integerp (q$ j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (q$-constraint))))

(local-defthm natp-r$
  (natp (r$))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (e$-constraint) :in-theory (enable r$))))

(local-defthm ratp-rho$
  (rationalp (rho$))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable rho$))))

(defund quot$ (j)
  (if (zp j)
      0
    (+ (quot$ (1- j))
       (* (q$ j) (expt (r$) (- 1 j))))))

(defund rem$ (j)
  (* (expt (r$) (1- j))
     (- (x$) (* (d$) (quot$ j)))))

(local-in-theory (disable (rem$) (quot$)))

(defthmd rem0-div-rewrite
  (equal (rem$ 0) (/ (x$) (r$)))
  :hints (("Goal" :in-theory (enable quot$ rem$))))

(defthmd rem-div-recurrence
  (implies (natp j)
           (equal (rem$ (+ 1 j))
                  (- (* (r$) (rem$ j))
                     (* (q$ (1+ j)) (d$)))))
  :hints (("Goal" :in-theory (enable rem$ quot$))))

(defthmd rem0-div-bound
  (< (abs (rem$ 0)) (* (rho$) (d$)))
  :hints (("Goal" :in-theory (enable r$ rho$ rem0-div-rewrite)
                  :cases ((= (e$) 1))
                  :nonlinearp t
                  :use (x$-constraint rho$-constraint e$-constraint))))

(defund sel-upper-div (k d) (* (+ k (rho$)) d))

(defund sel-lower-div (k d) (* (- k (rho$)) d))

(defthmd rem-div-bnd-next
  (implies (and (natp j)
                (<= (sel-lower-div (q$ (1+ j)) (d$)) (* (r$) (rem$ j)))
                (>= (sel-upper-div (q$ (1+ j)) (d$)) (* (r$) (rem$ j))))
           (<= (abs (rem$ (1+ j))) (* (rho$) (d$))))
  :hints (("Goal" :in-theory (enable sel-lower-div sel-upper-div rem-div-recurrence))))

(defthm select-overlap
  (implies (integerp k)
           (and (< (sel-lower-div k (d$)) (sel-lower-div (1+ k) (d$)))
                (< (sel-lower-div (1+ k) (d$)) (sel-upper-div k (d$)))
                (< (sel-upper-div k (d$)) (sel-upper-div (1+ k) (d$)))
		(<= (sel-upper-div k (d$)) (sel-lower-div (+ k 2) (d$)))))
  :hints (("Goal" :use (d$-constraint rho$-constraint)
                  :in-theory (enable sel-lower-div sel-upper-div))))

(local-defthmd r$-bound
  (>= (r$) 2)
  :hints (("Goal" :use (e$-constraint) :in-theory (enable r$))))

(local-defthmd a$+rho$-1
  (equal (a$)
         (/ (* (a$) (1- (r$)))
            (1- (r$))))
  :hints (("Goal" :use (r$-bound))))

(local-defthmd a$+rho$-2
  (equal (* (a$) (1- (r$)))
         (- (* (a$) (r$)) (a$))))

(local-defthmd a$+rho$-3
  (equal (a$)
         (/ (- (* (a$) (r$)) (a$))
            (1- (r$))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (a$+rho$-1 a$+rho$-2))))

(local-defthmd a$+rho$-4
  (equal (+ (/ (- (* (a$) (r$)) (a$))
               (1- (r$)))
            (rho$))
         (* (r$) (rho$)))
  :hints (("Goal" :use (r$-bound) :in-theory (enable rho$))))

(local-defthmd a$+rho$
  (equal (+ (a$) (rho$))
         (* (r$) (rho$)))
  :hints (("Goal" :use (a$+rho$-3 a$+rho$-4) :in-theory (theory 'minimal-theory))))

(defthmd div-containment
  (and (equal (sel-upper-div (a$) (d$)) (* (r$) (rho$) (d$)))
       (equal (sel-lower-div (- (a$)) (d$)) (- (* (r$) (rho$)(d$)))))
  :hints (("Goal" :use (a$+rho$) :in-theory (enable sel-lower-div sel-upper-div))))

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
                         (sel-upper-div k 9/8)))))
  :hints (("Goal" :in-theory (enable rho$ sel-lower-div sel-upper-div))))

(defthmd sel-limits-check-4
  (implies (and (<= 63/64 (d$))
                (<= (d$) 9/8)
                (= (r$) 4)
		(= (a$) 2)
                (member k '(-1 0 1 2)))
           (and (<= (+ (max (sel-lower-div k 63/64) (sel-lower-div k 9/8)) 1/8)
                    (md4 k))
                (>= (min (sel-upper-div k 63/64) (sel-upper-div k 9/8))
                    (md4 k))))
  :hints (("Goal" :in-theory (enable rho$ sel-lower-div sel-upper-div))))

(local-in-theory (disable (sel-lower-div) (sel-upper-div)))

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
                             (md4 (1+ k))))))
  :hints (("Goal" :use (sel-limits-4 sel-limits-check-4) :in-theory (enable rho$ sel-lower-div sel-upper-div))))

(local-defthmd r-bound-inv-1
  (implies (and (<= 63/64 (d$))
                (<= (d$) 9/8)
                (= (r$) 4)
		(= (a$) 2)
                (natp j)
                (<= (abs (rem$ j)) (* 2/3 (d$))))
           (and (<= (sel-lower-div -2 (d$)) (* 4 (rem$ j)))
                (>= (sel-upper-div 2 (d$)) (* 4 (rem$ j)))))
  :hints (("Goal" :in-theory (enable rho$) :use (div-containment))))

(local-defthmd r-bound-inv-2
  (implies (and (<= 63/64 (d$))
                (<= (d$) 9/8)
                (= (r$) 4)
		(= (a$) 2)
                (natp j)
                (<= (abs (rem$ j)) (* 2/3 (d$)))
                (rationalp a)
                (integerp (* 8 a))
                (< (abs (- a (* 4 (rem$ j)))) 1/8)
                (= (q$ (1+ j)) (select-digit-d4 a))
                (< (q$ (1+ j)) 2))
           (< a (md4 (1+ (q$ (1+ j))))))
  :hints (("Goal" :in-theory (enable select-digit-d4))))

(local-defthmd r-bound-inv-3
  (implies (and (rationalp a) (rationalp m)
                (integerp (* 8 a)) (integerp (* 8 m))
                (< a m))
           (<= a (- m 1/8))))

(local-defthmd r-bound-inv-4
  (implies (and (<= 63/64 (d$))
                (<= (d$) 9/8)
                (= (r$) 4)
		(= (a$) 2)
                (natp j)
                (<= (abs (rem$ j)) (* 2/3 (d$)))
                (rationalp a)
                (integerp (* 8 a))
                (< (abs (- a (* 4 (rem$ j)))) 1/8)
                (= (q$ (1+ j)) (select-digit-d4 a))
                (< (q$ (1+ j)) 2))
           (< (* 4 (rem$ j)) (md4 (1+ (q$ (1+ j))))))
  :hints (("Goal" :in-theory (enable select-digit-d4)
                  :use (r-bound-inv-2 (:instance r-bound-inv-3 (m (md4 (1+ (q$ (1+ j))))))))))

(local-defthmd r-bound-inv-5
  (implies (and (<= 63/64 (d$))
                (<= (d$) 9/8)
                (= (r$) 4)
		(= (a$) 2)
                (natp j)
                (<= (abs (rem$ j)) (* 2/3 (d$)))
                (rationalp a)
                (integerp (* 8 a))
                (< (abs (- a (* 4 (rem$ j)))) 1/8)
                (= (q$ (1+ j)) (select-digit-d4 a))
                (> (q$ (1+ j)) -2))
           (> (* 4 (rem$ j)) (- (md4 (q$ (1+ j))) 1/8)))
  :hints (("Goal" :in-theory (enable select-digit-d4))))

(local-defthmd r-bound-inv-6
  (implies (and (<= 63/64 (d$))
                (<= (d$) 9/8)
                (= (r$) 4)
		(= (a$) 2)
                (natp j)
                (<= (abs (rem$ j)) (* 2/3 (d$)))
                (rationalp a)
                (integerp (* 8 a))
                (< (abs (- a (* 4 (rem$ j)))) 1/8)
                (= (q$ (1+ j)) (select-digit-d4 a)))
	   (and (<= (sel-lower-div (q$ (1+ j)) (d$)) (* 4 (rem$ j)))
	        (>= (sel-upper-div (q$ (1+ j)) (d$)) (* 4 (rem$ j)))))
  :hints (("Goal" :in-theory (enable select-digit-d4)
                  :use (r-bound-inv-1 r-bound-inv-4 r-bound-inv-5
		        (:instance md4-k-bounds (k (q$ (1+ j))))))))

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
	   (<= (abs (rem$ (1+ j))) (* 2/3 (d$))))
  :hints (("Goal" :in-theory (enable rho$ select-digit-d4)
                  :use (rem-div-bnd-next (:instance r-bound-inv-6 (a approx))))))

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

(local-in-theory (disable (max-lower) (min-upper)))

(defthmd sel-limits-check-8
  (implies (and (= (r$) 8)
                (= (a$) 4)
                (bvecp i 6)
                (member k '(-3 -2 -1 0 1 2 3 4)))
           (and (<= (+ (max-lower i k) 1/64)
                    (md8 k i))
                (>= (min-upper i (1- k))
                    (md8 k i))))
  :hints (("Goal" :in-theory (enable rho$ md8 sel-lower-div sel-upper-div max-lower min-upper)
                  :use ((:instance bvecp-member (x i) (n 6))))))

(defund i64 (d) (fl (* 128 (- d 1/2))))

(local-in-theory (disable (i64)))

(local-defthmd bvecp-i$
  (implies (and (<= 1/2 (d$)) (< (d$) 1))
           (bvecp (i64 (d$)) 6))
  :hints (("Goal" :in-theory (enable bvecp i64))))

(local-defthmd d$-i$-bounds
  (implies (and (<= 1/2 (d$)) (< (d$) 1))
           (and (<= (+ 1/2 (/ (i64 (d$)) 128)) (d$))
                (< (d$) (+ 1/2 (/ (1+ (i64 (d$))) 128)))))
  :hints (("Goal" :in-theory (enable i64))))

(defthmd sel-limits-8
  (implies (and (= (r$) 8)
                (= (a$) 4)
		(<= 1/2 (d$))
		(< (d$) 1)
                (member k '(-4 -3 -2 -1 0 1 2 3 4)))
           (and (<= (sel-lower-div k (d$))
                    (max-lower (i64 (d$)) k))
                (>= (sel-upper-div k (d$))
                    (min-upper (i64 (d$)) k))))
  :hints (("Goal" :in-theory (enable rho$ max-lower min-upper sel-lower-div sel-upper-div)
           :use (d$-i$-bounds))))

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
                             (md8 (1+ k) (i64 (d$)))))))
  :hints (("Goal" :use (bvecp-i$ sel-limits-8
                        (:instance sel-limits-check-8 (i (i64 (d$))) (k (1+ k)))
                        (:instance sel-limits-check-8 (i (i64 (d$))))))))

(local-defthmd r-bound-inv-8-1
  (implies (and (= (r$) 8)
                (= (a$) 4)
                (natp j)
                (<= (abs (rem$ j)) (* 4/7 (d$))))
           (and (<= (sel-lower-div -4 (d$)) (* 8 (rem$ j)))
                (>= (sel-upper-div 4 (d$)) (* 8 (rem$ j)))))
  :hints (("Goal" :in-theory (enable rho$) :use (div-containment))))

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

(local-in-theory (disable (md8)))

(local-defthmd r-bound-inv-8-2
  (implies (and (= (r$) 8)
                (= (a$) 4)
                (natp j)
                (<= (abs (rem$ j)) (* 4/7 (d$)))
                (rationalp a)
                (integerp (* 64 a))
                (< (abs (- a (* 8 (rem$ j)))) 1/64)
                (= (q$ (1+ j)) (select-digit-d8 a (i64 (d$))))
                (< (q$ (1+ j)) 4))
           (< a (md8 (1+ (q$ (1+ j))) (i64 (d$)))))
  :hints (("Goal" :in-theory (enable rho$ select-digit-d8))))

(local-defthmd r-bound-inv-8-3
  (implies (and (rationalp a) (rationalp m)
                (integerp (* 64 a)) (integerp (* 64 m))
                (< a m))
           (<= a (- m 1/64))))

(local-defthm rat-m
  (implies (member k '(-3 -2 -1 0 1 2 3 4))
           (rationalp (md8 k i)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable md8))))

(local-defthm int-64-m
  (implies (member k '(-3 -2 -1 0 1 2 3 4))
           (integerp (* 64 (md8 k i))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable md8))))

(local-defthmd r-bound-inv-8-4
  (implies (and (= (r$) 8)
                (= (a$) 4)
                (natp j)
                (<= (abs (rem$ j)) (* 4/7 (d$)))
                (rationalp a)
                (integerp (* 64 a))
                (< (abs (- a (* 8 (rem$ j)))) 1/64)
                (= (q$ (1+ j)) (select-digit-d8 a (i64 (d$))))
                (< (q$ (1+ j)) 4))
           (< (* 8 (rem$ j)) (md8 (1+ (q$ (1+ j))) (i64 (d$)))))
  :hints (("Goal" :in-theory (enable select-digit-d8)
                  :use (r-bound-inv-8-2
		        (:instance r-bound-inv-8-3 (m (md8 (1+ (q$ (1+ j))) (i64 (d$)))))))))

(local-defthmd r-bound-inv-8-5
  (implies (and (= (r$) 8)
                (= (a$) 4)
                (natp j)
                (<= (abs (rem$ j)) (* 4/7 (d$)))
                (rationalp a)
                (integerp (* 64 a))
                (< (abs (- a (* 8 (rem$ j)))) 1/64)
                (= (q$ (1+ j)) (select-digit-d8 a (i64 (d$))))
                (> (q$ (1+ j)) -4))
           (> (* 8 (rem$ j)) (- (md8 (q$ (1+ j)) (i64 (d$))) 1/64)))
  :hints (("Goal" :in-theory (enable select-digit-d8))))

(local-defthmd r-bound-inv-8-6
  (implies (and (<= 1/2 (d$)) (< (d$) 1)
                (= (r$) 8)
                (= (a$) 4)
                (natp j)
                (<= (abs (rem$ j)) (* 4/7 (d$)))
                (rationalp a)
                (integerp (* 64 a))
                (< (abs (- a (* 8 (rem$ j)))) 1/64)
                (= (q$ (1+ j)) (select-digit-d8 a (i64 (d$)))))
	   (and (<= (sel-lower-div (q$ (1+ j)) (d$)) (* 8 (rem$ j)))
	        (>= (sel-upper-div (q$ (1+ j)) (d$)) (* 8 (rem$ j)))))
  :hints (("Goal" :in-theory (enable rho$ select-digit-d8)
                  :use (r-bound-inv-8-1 r-bound-inv-8-4 r-bound-inv-8-5
		        (:instance md8-k-bounds (k (q$ (1+ j))))))))

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
	   (<= (abs (rem$ (1+ j))) (* 4/7 (d$))))
  :hints (("Goal" :in-theory (enable rho$ select-digit-d8)
                  :use (rem-div-bnd-next (:instance r-bound-inv-8-6 (a approx))))))

;;------------------------------------------------------------------------------------------------------------------

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

(local-in-theory (disable (r%) (rho%)))

(local-defthm natp-e%
  (natp (e%))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (e%-constraint))))

(local-defthm ratp-x%
  (rationalp (x%))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (x%-constraint))))

(local-defthm intp-a%
  (integerp (a%))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (a%-constraint))))

(local-defthm intp-q%
  (implies (not (zp j))
           (integerp (q% j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (q%-constraint))))

(local-defthm natp-r%
  (natp (r%))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (e%-constraint) :in-theory (enable r%))))

(local-defthm ratp-rho%
  (rationalp (rho%))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable rho%))))

(defund quot% (j)
  (if (zp j)
      1
    (+ (quot% (1- j))
       (* (q% j) (expt (r%) (- j))))))

(defund rem% (j)
  (* (expt (r%) j)
     (- (x%) (* (quot% j) (quot% j)))))

(local-in-theory (disable (rem%) (quot%)))

(local-defthmd int-r%*n
  (implies (integerp n)
           (integerp (* (r%) n))))

(defthmd int-quot-sqrt
  (implies (natp j)
           (integerp (* (expt (r%) j) (quot% j))))
  :hints (("Goal" :in-theory (enable quot%) :induct (quot% j))
          ("Subgoal *1/2" :use ((:instance int-r%*n (n (* (QUOT% (+ -1 J)) (EXPT (r%) (+ -1 J)))))))))

(defthmd rem0-sqrt-rewrite
  (equal (rem% 0) (1- (x%)))
  :hints (("Goal" :in-theory (enable quot% rem%))))

(defthmd rem-sqrt-recurrence
  (implies (natp j)
           (equal (rem% (+ 1 j))
                  (- (* (r%) (rem% j))
                     (* (q% (1+ j))
		        (+ (* 2 (quot% j))
			   (* (expt (r%) (- (1+ j)))
			      (q% (1+ j))))))))
  :hints (("Goal" :in-theory (enable rem% quot%))))

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
  :rule-classes ()
  :hints (("Goal" :nonlinearp t :expand ((rem% j) (blo% j) (bhi% j)))))

(local-in-theory (disable (blo%) (bhi%)))

(local-defthmd r0-bounds-1
  (implies (and (rationalp q) (< -1/2 q) (<= q 0))
           (<= (1- (* q q)) -3/4))
  :hints (("Goal" :nonlinearp t)))

(defthmd rem0-sqrt-bounds
  (and (<= (blo% 0) (rem% 0))
       (>= (bhi% 0) (rem% 0)))
  :hints (("Goal" :in-theory (enable blo% bhi% quot% rem0-sqrt-rewrite)
           :use (x%-constraint rho%-constraint (:instance r0-bounds-1 (q (1- (rho%))))))))

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
  :rule-classes ()
  :hints (("Goal" :nonlinearp t
                  ;:use ((:instance q-vals (j (1+ j))))
		  :in-theory (enable rem% quot% blo% sel-lower-sqrt bhi% sel-upper-sqrt))))

(local-defthmd r%-bound
  (>= (r%) 2)
  :hints (("Goal" :use (e%-constraint) :in-theory (enable r%))))

(local-defthmd a%+rho%-1
  (equal (a%)
         (/ (* (a%) (1- (r%)))
            (1- (r%))))
  :hints (("Goal" :use (r%-bound))))

(local-defthmd a%+rho%-2
  (equal (* (a%) (1- (r%)))
         (- (* (a%) (r%)) (a%))))

(local-defthmd a%+rho%-3
  (equal (a%)
         (/ (- (* (a%) (r%)) (a%))
            (1- (r%))))
  :hints (("Goal" :in-theory (theory 'minimal-theory) :use (a%+rho%-1 a%+rho%-2))))

(local-defthmd a%+rho%-4
  (equal (+ (/ (- (* (a%) (r%)) (a%))
               (1- (r%)))
            (rho%))
         (* (r%) (rho%)))
  :hints (("Goal" :use (r%-bound) :in-theory (enable rho%))))

(local-defthmd a%+rho%
  (equal (+ (a%) (rho%))
         (* (r%) (rho%)))
  :hints (("Goal" :use (a%+rho%-3 a%+rho%-4) :in-theory (theory 'minimal-theory))))

(local-defthmd sqrt-containment-1
  (implies (natp j)
           (equal (sel-lower-sqrt (- (a%)) j)
                  (+ (- (* 2 (+ (a%) (rho%)) (quot% j)))
	             (* (+ (a%) (rho%)) (+ (a%) (rho%)) (expt (r%) (- (1+ j)))))))
  :hints (("Goal" :in-theory (enable blo% bhi% sel-lower-sqrt sel-upper-sqrt))))

(local-defthmd sqrt-containment-2
  (implies (natp j)
           (equal (sel-lower-sqrt (- (a%)) j)
                  (+ (- (* 2 (* (r%) (rho%)) (quot% j)))
	             (* (* (r%) (rho%)) (* (r%) (rho%)) (expt (r%) (- (1+ j)))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (a%+rho% sqrt-containment-1))))

(defthmd sqrt-containment
  (implies (natp j)
           (and (equal (sel-upper-sqrt (a%) j) (* (r%) (bhi% j)))
                (equal (sel-lower-sqrt (- (a%)) j) (* (r%) (blo% j)))))
  :hints (("Goal" :use (sqrt-containment-2 a%+rho%) :in-theory (enable blo% bhi% sel-upper-sqrt))))

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

(local-in-theory (disable (ms4) (i%) (quot%-bnds-inv) (rem%-bnds-inv) (approx%-bounds) (approx%-inv) (s4-inv) (s4-hyp)))

(local-defthmd rem%-bnds-1
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j))
           (and (<= (sel-lower-sqrt -2 j) (* 4 (rem% j)))
	        (>= (sel-upper-sqrt 2 j) (* 4 (rem% j)))))
  :hints (("Goal" :in-theory (enable s4-hyp s4-inv rem%-bnds-inv)
                  :use (sqrt-containment)
		  :nonlinearp t)))

(local-defthmd rem%-bnds-2
  (implies (and (= (r%) 4) (= (a%) 2)
		(approx%-inv 0))
	   (member (q% 1) '(-2 -1 0)))
  :hints (("Goal" :in-theory (enable approx%-inv approx%-bounds i% quot% select-digit-s4 ms4 rem0-sqrt-rewrite)
                  :use (x%-constraint)
		  :nonlinearp t)))

(local-in-theory (disable (sel-upper-sqrt) (sel-lower-sqrt)))

(local-defthm rem%-bnds-3
  (implies (and (= (r%) 4) (= (a%) 2)
		(approx%-inv 0))
	   (and (or (= (q% 1) 2)
	            (<= (ms4 (i% 0) 0 (1+ (q% 1))) (sel-upper-sqrt (q% 1) 0)))
	        (or (= (q% 1) -2)
		    (>= (ms4 (i% 0) 0 (q% 1)) (+ (sel-lower-sqrt (q% 1) 0) 1/32)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable quot% rho% i% sel-upper-sqrt sel-lower-sqrt select-digit-s4 ms4)
                  :use (rem%-bnds-2))))

(local-defthm rem%-bnds-4
  (implies (and (= (r%) 4)
                (= (a%) 2)
		(s4-hyp 1))
           (member (i% 1) '(0 4 8)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable s4-hyp s4-inv quot%-bnds-inv quot% i%))))

(local-defthmd rem%-bnds-5
  (implies (and (= (r%) 4) (= (a%) 2))
           (equal (quot% 1) (+ 1/2 (/ (i% 1) 16))))
  :hints (("Goal" :in-theory (enable i%))))

(local-defthmd rem%-bnds-6
  (implies (and (= (r%) 4) (= (a%) 2))
           (equal (quot% 2) (+ 1/2 (/ (i% 2) 16))))
  :hints (("Goal" :use (rem%-bnds-4) :in-theory (enable i%))))

(local-defthmd q%-vals
  (implies (and (= (r%) 4) (= (a%) 2)
                (not (zp j)))
           (member (q% j) '(-2 -1 0 1 2)))
  :hints (("Goal" :use (q%-constraint
			(:instance bvecp-member (x (q% j)) (n 2))
			(:instance bvecp-member (x (- (q% j))) (n 2)))
                  :in-theory (enable bvecp))))

(local-defthmd rem%-bnds-7
  (implies (and (= (r%) 4) (= (a%) 2)
                (quot%-bnds-inv 2))
           (member (i% 2) '(0 1 2 3 4 5 6 7 8)))
  :hints (("Goal" :use ((:instance q%-vals (j 1))
                        (:instance q%-vals (j 2)))
                  :in-theory (enable bvecp quot%-bnds-inv i% quot%))))

(local-defthm rem%-bnds-8
  (implies (and (= (r%) 4)
                (= (a%) 2)
		(s4-hyp 1))
	   (and (or (= (q% 2) 2)
	            (<= (ms4 (i% 1) 1 (1+ (q% 2))) (sel-upper-sqrt (q% 2) 1)))
	        (or (= (q% 2) -2)
		    (>= (ms4 (i% 1) 1 (q% 2)) (+ (sel-lower-sqrt (q% 2) 1) 1/32)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho% sel-lower-sqrt sel-upper-sqrt i% select-digit-s4 ms4)
                  :use (rem%-bnds-4 rem%-bnds-5 (:instance q%-vals (j 2))))))

(local-defthm rem%-bnds-9
  (implies (and (= (r%) 4) (= (a%) 2)
                (quot%-bnds-inv 2))
	   (and (or (= (q% 3) 2)
	            (<= (ms4 (i% 2) 2 (1+ (q% 3))) (sel-upper-sqrt (q% 3) 2)))
	        (or (= (q% 3) -2)
		    (>= (ms4 (i% 2) 2 (q% 3)) (+ (sel-lower-sqrt (q% 3) 2) 1/32)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho% sel-lower-sqrt sel-upper-sqrt i% select-digit-s4 ms4)
                  :use (rem%-bnds-6 rem%-bnds-7 (:instance q%-vals (j 3))))))

(local-defthmd rem%-bnds-10
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 3)
		(rationalp z)
	        (<= (abs (- (quot% (1- j)) (quot% 2)))
		    z))
	   (<= (abs (- (quot% j) (quot% 2)))
	       (+ z (* 2 (expt 4 (- j))))))
  :hints (("Goal" :in-theory (enable quot%) :use (q%-vals) :nonlinearp t)))

(local-defthmd rem%-bnds-11
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 3))
	   (equal (+ (/ (- 1 (expt 4 (- 2 (1- j)))) 24)
	             (* 2 (expt 4 (- j))))
		  (/ (- 1 (- (expt 4 (- 3 j)) (* 3 (expt 4 (- 2 j))))) 24))))

(local-defthmd rem%-bnds-12
  (implies (integerp n)
           (equal (expt 4 n)
	          (expt 2 (* 2 n)))))

(local-defthmd rem%-bnds-13
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 3))
	   (equal (- (expt 4 (- 3 j)) (* 3 (expt 4 (- 2 j))))
	          (expt 4 (- 2 j))))
  :hints (("Goal" :use ((:instance rem%-bnds-12 (n (- 3 j)))))))

(local-defthmd rem%-bnds-14
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 3)
		(rationalp (/ (- 1 (expt 4 (- 2 (1- j)))) 24))
	        (<= (abs (- (quot% (1- j)) (quot% 2)))
		    (/ (- 1 (expt 4 (- 2 (1- j)))) 24)))
	   (<= (abs (- (quot% j) (quot% 2)))
	       (/ (- 1 (expt 4 (- 2 j))) 24)))
  :hints (("Goal" :use (rem%-bnds-11 rem%-bnds-13
                        (:instance rem%-bnds-10 (z (/ (- 1 (expt 4 (- 2 (1- j)))) 24))))
		  :in-theory (theory 'minimal-theory))))

(local-defthmd rem%-bnds-15
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 3)
	        (<= (abs (- (quot% (1- j)) (quot% 2)))
		    (/ (- 1 (expt 4 (- 2 (1- j)))) 24)))
	   (<= (abs (- (quot% j) (quot% 2)))
	       (/ (- 1 (expt 4 (- 2 j))) 24)))
  :hints (("Goal" :use (rem%-bnds-14))))

(local-defthmd rem%-bnds-16
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 3))
	   (<= (abs (- (quot% j) (quot% 2)))
	       (/ (- 1 (expt 4 (- 2 j))) 24)))
  :hints (("Goal" :in-theory (enable quot%) :induct (quot% j))
          ("Subgoal *1/2" :use (rem%-bnds-15) :in-theory (disable abs))))

(local-defthmd rem%-bnds-17
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 3))
	   (< (abs (- (quot% j) (quot% 2)))
	      1/24))
  :hints (("Goal" :use (rem%-bnds-16) :nonlinearp t)))

(local-defthmd rem%-bnds-18
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 4)
		(rationalp z)
	        (<= (abs (- (quot% (1- j)) (quot% 3)))
		    z))
	   (<= (abs (- (quot% j) (quot% 3)))
	       (+ z (* 2 (expt 4 (- j))))))
  :hints (("Goal" :in-theory (enable quot%) :use (q%-vals) :nonlinearp t)))

(local-defthmd rem%-bnds-19
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 4))
	   (equal (+ (/ (- 1 (expt 4 (- 3 (1- j)))) 96)
	             (* 2 (expt 4 (- j))))
		  (/ (- 1 (- (expt 4 (- 4 j)) (* 3 (expt 4 (- 3 j))))) 96))))

(local-defthmd rem%-bnds-20
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 3))
	   (equal (- (expt 4 (- 4 j)) (* 3 (expt 4 (- 3 j))))
	          (expt 4 (- 3 j))))
  :hints (("Goal" :use ((:instance rem%-bnds-12 (n (- 4 j)))))))

(local-defthmd rem%-bnds-21
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 4)
		(rationalp (/ (- 1 (expt 4 (- 3 (1- j)))) 96))
	        (<= (abs (- (quot% (1- j)) (quot% 3)))
		    (/ (- 1 (expt 4 (- 3 (1- j)))) 96)))
	   (<= (abs (- (quot% j) (quot% 3)))
	       (/ (- 1 (expt 4 (- 3 j))) 96)))
  :hints (("Goal" :use (rem%-bnds-19 rem%-bnds-20
                        (:instance rem%-bnds-18 (z (/ (- 1 (expt 4 (- 3 (1- j)))) 96))))
		  :in-theory (theory 'minimal-theory))))

(local-defthmd rem%-bnds-22
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 4)
	        (<= (abs (- (quot% (1- j)) (quot% 3)))
		    (/ (- 1 (expt 4 (- 3 (1- j)))) 96)))
	   (<= (abs (- (quot% j) (quot% 3)))
	       (/ (- 1 (expt 4 (- 3 j))) 96)))
  :hints (("Goal" :use (rem%-bnds-21))))

(local-defthmd rem%-bnds-23
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 4))
	   (<= (abs (- (quot% j) (quot% 3)))
	       (/ (- 1 (expt 4 (- 3 j))) 96)))
  :hints (("Goal" :in-theory (enable quot%) :induct (quot% j))
          ("Subgoal *1/2" :use (rem%-bnds-22) :in-theory (disable abs))))

(local-defthmd rem%-bnds-24
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(>= j 3))
	   (< (abs (- (quot% j) (quot% 3)))
	      1/96))
  :hints (("Goal" :use (rem%-bnds-23) :nonlinearp t)))

(local-defthmd rem%-bnds-25
  (implies (and (= (r%) 4) (= (a%) 2)
                (= (i% 2) 1))
	   (and (equal (quot% 2) 9/16)
	        (equal (q% 1) -2)
		(equal (q% 2) 1)
		(equal (quot% 1) 1/2)))
  :hints (("Goal" :expand ((quot% 0) (quot% 1) (quot% 2))
                  :use (rem%-bnds-6 (:instance q%-vals (j 1)) (:instance q%-vals (j 2))))))

(local-defthmd rem%-bnds-26
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 1)
                (= (i% 2) 1))
	   (< (* 4 (rem% 1)) 3/2))
  :hints (("Goal" :in-theory (enable approx%-inv approx%-bounds select-digit-s4 ms4)
                  :use (rem%-bnds-5 rem%-bnds-25))))

(local-defthmd rem%-bnds-27
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 1)
                (= (i% 2) 1))
	   (< (x%) 11/32))
  :hints (("Goal" :in-theory (enable rem%)
                  :use (rem%-bnds-25 rem%-bnds-26)
		  :nonlinearp t)))

(local-defthmd rem%-bnds-28
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 2)
                (= (i% 2) 1)
                (= (q% 3) 2))
	   (> (* 4 (rem% 2)) 7/4))
  :hints (("Goal" :in-theory (enable approx%-inv approx%-bounds select-digit-s4 ms4))))

(local-defthmd rem%-bnds-29
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 1)
                (approx%-inv 2)
                (= (i% 2) 1))
           (not (= (q% 3) 2)))
  :hints (("Goal" :in-theory (enable rem%)
                  :use (rem%-bnds-25 rem%-bnds-27 rem%-bnds-28)
		  :nonlinearp t)))

(local-defthmd rem%-bnds-30
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 1)
                (approx%-inv 2)
                (= (i% 2) 1)
		(natp j)
		(>= j 3))
           (< (quot% j) 113/192))
  :hints (("Goal" :expand ((quot% 3))
                  :use (rem%-bnds-24 rem%-bnds-25 rem%-bnds-29 (:instance q%-vals (j 3))))))

(local-defund qmin (i)
  (max 1/2 (+ 11/24 (/ i 16))))

(local-defund qmax (i)
  (if (= i 1)
      113/192
    (+ 13/24 (/ i 16))))

(local-defthmd rem%-bnds-31
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 1)
                (approx%-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3))
	   (and (<= (qmin (i% 2)) (quot% j))
	        (>= (qmax (i% 2)) (quot% j))))
  :hints (("Goal" :use (rem%-bnds-7 rem%-bnds-6 rem%-bnds-17 rem%-bnds-30)
                  :in-theory (enable quot%-bnds-inv qmin qmax))))

(local-defthmd rem%-bnds-32
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 1)
                (approx%-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3)
		(member k '(1 2)))
	   (and (>= (sel-upper-sqrt (1- k) j)
	           (* 2 (qmin (i% 2)) (- k 1/3)))
		(<= (sel-lower-sqrt k j)
		   (+ (* 2 (qmax (i% 2)) (- k 2/3))
		      (* 1/256 (- k 2/3) (- k 2/3))))))
  :hints (("Goal" :in-theory (enable rho% sel-lower-sqrt sel-upper-sqrt qmin qmax)
                  :use (rem%-bnds-7 rem%-bnds-31)
		  :nonlinearp t)))

(local-defthmd rem%-bnds-33
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 1)
                (approx%-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3)
		(member k '(-1 0)))
	   (and (>= (sel-upper-sqrt (1- k) j)
	           (* 2 (qmax (i% 2)) (- k 1/3)))
		(<= (sel-lower-sqrt k j)
		   (+ (* 2 (qmin (i% 2)) (- k 2/3))
		      (* 1/256 (- k 2/3) (- k 2/3))))))
  :hints (("Goal" :in-theory (enable rho% sel-lower-sqrt sel-upper-sqrt qmin qmax)
                  :use (rem%-bnds-7 rem%-bnds-31)
		  :nonlinearp t)))

(local-defthmd rem%-bnds-34
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 1)
                (approx%-inv 2)
		(quot%-bnds-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3)
		(member k '(-1 0 1 2)))
	   (and (>= (sel-upper-sqrt (1- k) j)
	            (ms4 (i% 2) j k))
		(<= (+ (sel-lower-sqrt k j) 1/32)
		    (ms4 (i% 2) j k))))
  :hints (("Goal" :in-theory (enable rho% qmin qmax ms4)
                  :use (rem%-bnds-7 rem%-bnds-32 rem%-bnds-33)
		  :nonlinearp t)))

(local-defthm i-j-2
  (implies (and (natp j)
                (>= j 3))
	   (equal (i% j) (i% 2)))
  :hints (("Goal" :in-theory (enable quot% i%) :induct (quot% j))))

(local-defthm rem%-bnds-35
  (implies (and (= (r%) 4) (= (a%) 2)
                (approx%-inv 1)
                (approx%-inv 2)
		(quot%-bnds-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3))
	   (and (or (= (q% (1+ j)) 2)
	            (<= (ms4 (i% j) j (1+ (q% (1+ j)))) (sel-upper-sqrt (q% (1+ j)) j)))
	        (or (= (q% (1+ j)) -2)
		    (>= (ms4 (i% j) j (q% (1+ j))) (+ (sel-lower-sqrt (q% (1+ j)) j) 1/32)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance q%-vals (j (1+ j)))
                        (:instance rem%-bnds-34 (k (q% (1+ j))))
                        (:instance rem%-bnds-34 (k (1+ (q% (1+ j)))))
                        (:instance q%-vals (j (1+ j)))))))

(local-defthmd hyp-inv
  (implies (and (natp j)
                (natp k)
		(<= k j)
		(s4-hyp j))
	   (s4-inv k))
  :hints (("Goal" :in-theory (enable s4-hyp) :induct (s4-hyp j))))

(local-defthm rem%-bnds-36
  (implies (and (= (r%) 4) (= (a%) 2)
		(natp j)
		(>= j 3)
		(s4-hyp j))
	   (and (or (= (q% (1+ j)) 2)
	            (<= (ms4 (i% j) j (1+ (q% (1+ j)))) (sel-upper-sqrt (q% (1+ j)) j)))
	        (or (= (q% (1+ j)) -2)
		    (>= (ms4 (i% j) j (q% (1+ j))) (+ (sel-lower-sqrt (q% (1+ j)) j) 1/32)))))
  :rule-classes ()
  :hints (("Goal" :use (rem%-bnds-35
                        (:instance hyp-inv (k j))
                        (:instance hyp-inv (k 1))
                        (:instance hyp-inv (k 2))
                        (:instance hyp-inv (k 3)))
		  :in-theory '(natp s4-inv zp))))

(local-defthm rem%-bnds-37
  (implies (natp j)
           (or (= j 0) (= j 1) (= j 2) (>= j 3)))
  :rule-classes ())

(local-defthm rem%-bnds-38
  (implies (and (= (r%) 4) (= (a%) 2)
		(or (= j 0) (= j 1) (= j 2))
		(s4-hyp j))
	   (and (or (= (q% (1+ j)) 2)
	            (<= (ms4 (i% j) j (1+ (q% (1+ j)))) (sel-upper-sqrt (q% (1+ j)) j)))
	        (or (= (q% (1+ j)) -2)
		    (>= (ms4 (i% j) j (q% (1+ j))) (+ (sel-lower-sqrt (q% (1+ j)) j) 1/32)))))
  :rule-classes ()
  :hints (("Goal" :use (rem%-bnds-3 rem%-bnds-8 rem%-bnds-9)
                  :in-theory '(s4-inv s4-hyp zp))))

(local-defthm rem%-bnds-39
  (implies (and (= (r%) 4) (= (a%) 2)
		(natp j)
		(s4-hyp j))
	   (and (or (= (q% (1+ j)) 2)
	            (<= (ms4 (i% j) j (1+ (q% (1+ j)))) (sel-upper-sqrt (q% (1+ j)) j)))
	        (or (= (q% (1+ j)) -2)
		    (>= (ms4 (i% j) j (q% (1+ j))) (+ (sel-lower-sqrt (q% (1+ j)) j) 1/32)))))
  :rule-classes ()
  :hints (("Goal" :use (rem%-bnds-36 rem%-bnds-37 rem%-bnds-38)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd rem%-bnds-40
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j))
           (and (<= (sel-lower-sqrt (q% (1+ j)) j) (* 4 (rem% j)))
	        (>= (sel-upper-sqrt (q% (1+ j)) j) (* 4 (rem% j)))))
  :hints (("Goal" :in-theory (enable select-digit-s4 approx%-inv approx%-bounds)
                  :use (rem%-bnds-1 rem%-bnds-39))))

(local-defthmd rem%-bnds-41
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(s4-hyp j))
           (and (<= (sel-lower-sqrt (q% (1+ j)) j) (* 4 (rem% j)))
	        (>= (sel-upper-sqrt (q% (1+ j)) j) (* 4 (rem% j)))))
  :hints (("Goal" :in-theory (enable s4-hyp s4-inv)
                  :use (rem%-bnds-40))))

(local-defthmd rem%-bnds
  (implies (and (= (r%) 4) (= (a%) 2)
                (natp j)
		(s4-hyp j))
           (rem%-bnds-inv (1+ j)))
  :hints (("Goal" :in-theory '(rem%-bnds-inv)
                  :use (rem-sqrt-bnds-next rem%-bnds-41))))

(local-defthmd quot%-bnds-1
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j)
		(= (quot% j) 1/2))
	   (>= (quot% (1+ j)) 1/2))
  :hints (("Goal" :in-theory (enable rem% quot% approx%-bounds approx%-inv ms4 select-digit-s4)
                  :use (x%-constraint)
		  :nonlinearp t)))

(local-defthmd quot%-bnds-2-1
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j)
		(= (quot% j) 1))
	   (and (< (* 4 (rem% j)) (- (ms4 (i% j) j 2) 1/32))
	        (< (* 4 (rem% j)) (- (ms4 (i% j) j 1) 1/32))))
  :hints (("Goal" :in-theory (enable i% rem% s4-inv approx%-inv ms4)
                  :use (rem%-bnds-4 rem%-bnds-7 rem%-bnds-37 x%-constraint
		        (:instance hyp-inv (k 2)))
		  :nonlinearp t)))

(local-defthmd quot%-bnds-2-2
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j)
		(= (quot% j) 1))
	   (and (< (approx% j) (ms4 (i% j) j 2))
	        (< (approx% j) (ms4 (i% j) j 1))))
  :hints (("Goal" :in-theory (enable approx%-bounds approx%-inv)
                  :use (quot%-bnds-2-1))))

(local-defthmd quot%-bnds-2
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j)
		(= (quot% j) 1))
	   (<= (quot% (1+ j)) 1))
  :hints (("Goal" :in-theory (enable quot% approx%-inv select-digit-s4)
                  :use (quot%-bnds-2-2)
		  :nonlinearp t)))

(local-defthmd quot%-bnds-3
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j)
		(> (quot% j) 1/2))
	   (> (* (expt 4 j) (quot% j)) (* 1/2 (expt 4 j))))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd quot%-bnds-4
  (implies (not (zp j))
	   (integerp (* 1/2 (expt 4 j)))))

(local-defthmd quot%-bnds-5
  (implies (and (integerp a) (integerp b) (> a b))
           (>= a (1+ b))))

(local-defthmd quot%-bnds-6
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (not (zp j))
		(s4-hyp j)
		(approx%-inv j)
		(> (quot% j) 1/2))
	   (>= (* (expt 4 j) (quot% j)) (1+ (* 1/2 (expt 4 j)))))
  :hints (("Goal" :use (int-quot-sqrt quot%-bnds-3 quot%-bnds-4
                        (:instance quot%-bnds-5 (a (* (expt 4 j) (quot% j))) (b (* 1/2 (expt 4 j))))))))

(local-defthmd quot%-bnds-7
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (not (zp j))
		(s4-hyp j)
		(approx%-inv j)
		(> (quot% j) 1/2))
	   (>= (quot% j) (+ 1/2 (expt 4 (- j)))))
  :hints (("Goal" :use (quot%-bnds-6)
		  :nonlinearp t)))

(local-defthmd quot%-bnds-8
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j)
		(>= (quot% j) 1/2))
	   (>= (quot% (1+ j)) 1/2))
  :hints (("Goal" :expand ((quot% 0) (quot% 1) (quot% (+ 1 j)))
                  :nonlinearp t
		  :use (quot%-bnds-1 quot%-bnds-7 (:instance q%-vals (j (1+ j)))))))

(local-defthmd quot%-bnds-9
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j)
		(< (quot% j) 1))
	   (< (* (expt 4 j) (quot% j)) (expt 4 j)))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd quot%-bnds-10
  (implies (and (integerp a) (integerp b) (< a b))
           (<= a (1- b))))

(local-defthmd quot%-bnds-11
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (not (zp j))
		(s4-hyp j)
		(approx%-inv j)
		(< (quot% j) 1))
	   (<= (* (expt 4 j) (quot% j)) (1- (expt 4 j))))
  :hints (("Goal" :use (int-quot-sqrt quot%-bnds-9
                        (:instance quot%-bnds-10 (a (* (expt 4 j) (quot% j))) (b (expt 4 j)))))))

(local-defthmd quot%-bnds-12
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (not (zp j))
		(s4-hyp j)
		(approx%-inv j)
		(< (quot% j) 1))
	   (<= (quot% j) (- 1 (expt 4 (- j)))))
  :hints (("Goal" :use (quot%-bnds-11)
		  :nonlinearp t)))

(local-defthmd quot%-bnds-13
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j)
		(approx%-inv j)
		(<= (quot% j) 1))
	   (<= (quot% (1+ j)) 1))
  :hints (("Goal" :expand ((quot% 0) (quot% 1) (quot% (+ 1 j)))
                  :nonlinearp t
		  :use (quot%-bnds-2 quot%-bnds-12 (:instance q%-vals (j (1+ j)))))))

(local-defthmd quot%-bnds
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j))
	   (quot%-bnds-inv (1+ j)))
  :hints (("Goal" :in-theory (enable s4-inv quot%-bnds-inv)
		  :use (quot%-bnds-8 quot%-bnds-13 (:instance hyp-inv (k j))))))

(defthmd srt-sqrt-rad-4
  (implies (and (= (r%) 4)
                (= (a%) 2)
                (natp j)
		(s4-hyp j))
	   (and (quot%-bnds-inv (1+ j))
                (rem%-bnds-inv (1+ j))))
  :hints (("Goal" :use (rem%-bnds quot%-bnds))))

;;------------------------------------------------------------------------------------------------------------------

(defun ms8-0 (k)
  (nth (- 1 k) '(0 -64 -176 -272 -352)))

(defun ms8-1 (i k)
  (nth (- 4 k) (nth (/ i 8) '((236 166 96 31 -32 -92 -152 -212)
                              (291 206 121 41 -42 -122 -192 -267)
                              (351 241 141 46 -47 -142 -232 -322)
                              (406 281 171 61 -62 -172 -277 -377)
                              (461 326 191 61 -62 -192 -317 -442)))))
#|
(defun ms8-1 (i k)
  (nth (- 4 k) (nth (/ i 8) '((237 167 97 32 -32 -92 -152 -212)
                              (292 207 122 42 -42 -122 -192 -267)
                              (352 242 142 47 -47 -142 -232 -322)
                              (407 282 172 62 -62 -172 -277 -377)
                              (462 327 192 62 -62 -192 -317 -442)))))
|#

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

#|
(defun ms8-2 (i k)
  (nth (- 4 k) (nth i '((226 161 97 32 -32 -97 -161 -225)
                        (231 165 99 33 -33 -99 -165 -231)
                        (238 170 102 34 -34 -102 -170 -238)
                        (245 175 105 35 -35 -105 -175 -245)
                        (252 180 108 36 -36 -108 -180 -252)
                        (259 185 111 37 -37 -111 -185 -259)
                        (266 190 114 38 -38 -114 -190 -266)
                        (273 195 117 39 -39 -117 -195 -273)
                        (280 200 120 40 -40 -120 -200 -280)
                        (287 205 123 41 -41 -123 -205 -287)
                        (294 210 126 42 -42 -126 -210 -294)
                        (301 215 129 43 -43 -129 -215 -301)
                        (308 220 132 44 -44 -132 -220 -308)
                        (315 225 135 45 -45 -135 -225 -315)
                        (322 230 138 46 -46 -138 -230 -322)
                        (329 235 141 47 -47 -141 -235 -329)
                        (336 240 144 48 -48 -144 -240 -336)
                        (343 245 147 49 -49 -147 -245 -343)
                        (350 250 150 50 -50 -150 -250 -350)
                        (357 255 153 51 -51 -153 -255 -357)
                        (364 260 156 52 -52 -156 -260 -364)
                        (371 265 159 53 -53 -159 -265 -371)
                        (378 270 162 54 -54 -162 -270 -378)
                        (385 275 165 55 -55 -165 -275 -385)
                        (392 280 168 56 -56 -168 -280 -392)
                        (399 285 171 57 -57 -171 -285 -399)
                        (406 290 174 58 -58 -174 -290 -406)
                        (413 295 177 59 -59 -177 -295 -413)
                        (420 300 180 60 -60 -180 -300 -420)
                        (427 305 183 61 -61 -183 -305 -427)
                        (434 310 186 62 -62 -186 -310 -434)
                        (441 315 189 63 -63 -189 -315 -441)
                        (447 319 191 64 -63 -191 -318 -446)))))
|#

(defun ms8*64 (i j k)
  (case j
    (0 (ms8-0 k))
    (1 (ms8-1 i k))
    (t (ms8-2 i k))))

(defund ms8 (i j k)
  (/ (ms8*64 i j k) 64))

(local (in-theory (enable ms8)))

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

(local-in-theory (disable (ms8) (i8%) (quot%-bnds-inv) (rem%-bnds-inv) (approx8%-bounds) (approx8%-inv) (s8-inv) (s8-hyp)))

(local-defthmd rem%-8-bnds-1
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(s8-hyp j)
		(approx8%-inv j))
           (and (<= (sel-lower-sqrt -4 j) (* 8 (rem% j)))
	        (>= (sel-upper-sqrt 4 j) (* 8 (rem% j)))))
  :hints (("Goal" :in-theory (enable s8-inv s8-hyp rem%-bnds-inv)
                  :use (sqrt-containment)
		  :nonlinearp t)))

(local-defthmd rem%-8-bnds-2
  (implies (and (= (r%) 8) (= (a%) 4)
		(approx8%-inv 0))
	   (member (q% 1) '(-4 -3 -2 -1 0)))
  :hints (("Goal" :in-theory (enable approx8%-inv approx8%-bounds i8% quot% select-digit-s8 ms8 rem0-sqrt-rewrite)
                  :use (x%-constraint)
		  :nonlinearp t)))

(local-defthm rem%-8-bnds-3
  (implies (and (= (r%) 8) (= (a%) 4)
		(approx8%-inv 0))
	   (and (or (= (q% 1) 4)
	            (<= (ms8 (i8% 0) 0 (1+ (q% 1))) (sel-upper-sqrt (q% 1) 0)))
	        (or (= (q% 1) -4)
		    (>= (ms8 (i8% 0) 0 (q% 1)) (+ (sel-lower-sqrt (q% 1) 0) 1/128)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable quot% rho% i8% sel-upper-sqrt sel-lower-sqrt select-digit-s8 ms8)
                  :use (rem%-8-bnds-2))))

(local-defthm rem%-8-bnds-4
  (implies (and (= (r%) 8)
                (= (a%) 4)
		(s8-hyp 1))
           (member (i8% 1) '(0 8 16 24 32)))
  :rule-classes ()
  :hints (("Goal" :use (rem%-8-bnds-2)
                  :in-theory (enable s8-hyp s8-inv quot%-bnds-inv quot% i8%))))

(local-defthmd rem%-8-bnds-5
  (implies (and (= (r%) 8) (= (a%) 4))
           (equal (quot% 1) (+ 1/2 (/ (i8% 1) 64))))
  :hints (("Goal" :in-theory (enable i8%))))

(local-defthmd rem%-8-bnds-6
  (implies (and (= (r%) 8) (= (a%) 4))
           (equal (quot% 2) (+ 1/2 (/ (i8% 2) 64))))
  :hints (("Goal" :use (rem%-8-bnds-4) :in-theory (enable i8%))))

(local-defthmd q%-8-vals
  (implies (and (= (r%) 8) (= (a%) 4)
                (not (zp j)))
           (member (q% j) '(-4 -3 -2 -1 0 1 2 3 4)))
  :hints (("Goal" :use (q%-constraint
			(:instance bvecp-member (x (q% j)) (n 3))
			(:instance bvecp-member (x (- (q% j))) (n 3)))
                  :in-theory (enable bvecp))))

(local-defthmd rem%-8-bnds-7
  (implies (and (= (r%) 8) (= (a%) 4)
                (quot%-bnds-inv 2))
           (member (i8% 2) (nats 33)))
  :hints (("Goal" :use ((:instance q%-8-vals (j 1))
                        (:instance q%-8-vals (j 2)))
                  :in-theory (enable bvecp quot%-bnds-inv i8% quot%))))

(local-defthm rem%-8-bnds-8
  (implies (and (= (r%) 8)
                (= (a%) 4)
		(s8-hyp 1))
	   (and (or (= (q% 2) 4)
	            (<= (ms8 (i8% 1) 1 (1+ (q% 2))) (sel-upper-sqrt (q% 2) 1)))
	        (or (= (q% 2) -4)
		    (>= (ms8 (i8% 1) 1 (q% 2)) (+ (sel-lower-sqrt (q% 2) 1) 1/128)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho% sel-lower-sqrt sel-upper-sqrt i8% select-digit-s8 ms8)
                  :use (rem%-8-bnds-4 rem%-8-bnds-5 (:instance q%-8-vals (j 2))))))

(local-defthm rem%-8-bnds-9
  (implies (and (= (r%) 8) (= (a%) 4)
                (quot%-bnds-inv 2))
	   (and (or (= (q% 3) 4)
	            (<= (ms8 (i8% 2) 2 (1+ (q% 3))) (sel-upper-sqrt (q% 3) 2)))
	        (or (= (q% 3) -4)
		    (>= (ms8 (i8% 2) 2 (q% 3)) (+ (sel-lower-sqrt (q% 3) 2) 1/128)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rho% sel-lower-sqrt sel-upper-sqrt i8% select-digit-s8 ms8)
                  :use (rem%-8-bnds-6 rem%-8-bnds-7 (:instance q%-8-vals (j 3))))))

(local-defthmd rem%-8-bnds-10
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(>= j 3)
		(rationalp z)
	        (<= (abs (- (quot% (1- j)) (quot% 2)))
		    z))
	   (<= (abs (- (quot% j) (quot% 2)))
	       (+ z (* 4 (expt 8 (- j))))))
  :hints (("Goal" :in-theory (enable quot%) :use (q%-8-vals) :nonlinearp t)))

(local-defthmd rem%-8-bnds-11
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(>= j 3))
	   (equal (+ (/ (- 1 (expt 8 (- 2 (1- j)))) 112)
	             (* 4 (expt 8 (- j))))
		  (/ (- 1 (- (expt 8 (- 3 j)) (* 7 (expt 8 (- 2 j))))) 112))))

(local-defthmd rem%-8-bnds-12
  (implies (integerp n)
           (equal (expt 8 n)
	          (expt 2 (* 3 n)))))

(local-defthmd rem%-8-bnds-13
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(>= j 3))
	   (equal (- (expt 8 (- 3 j)) (* 7 (expt 8 (- 2 j))))
	          (expt 8 (- 2 j))))
  :hints (("Goal" :use ((:instance rem%-8-bnds-12 (n (- 3 j)))))))

(local-defthmd rem%-8-bnds-14
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(>= j 3)
		(rationalp (/ (- 1 (expt 8 (- 2 (1- j)))) 112))
	        (<= (abs (- (quot% (1- j)) (quot% 2)))
		    (/ (- 1 (expt 8 (- 2 (1- j)))) 112)))
	   (<= (abs (- (quot% j) (quot% 2)))
	       (/ (- 1 (expt 8 (- 2 j))) 112)))
  :hints (("Goal" :use (rem%-8-bnds-11 rem%-8-bnds-13
                        (:instance rem%-8-bnds-10 (z (/ (- 1 (expt 8 (- 2 (1- j)))) 112))))
		  :in-theory (theory 'minimal-theory))))

(local-defthmd rem%-8-bnds-15
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(>= j 3)
	        (<= (abs (- (quot% (1- j)) (quot% 2)))
		    (/ (- 1 (expt 8 (- 2 (1- j)))) 112)))
	   (<= (abs (- (quot% j) (quot% 2)))
	       (/ (- 1 (expt 8 (- 2 j))) 112)))
  :hints (("Goal" :use (rem%-8-bnds-14))))

(local-defthmd rem%-8-bnds-16
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(>= j 3))
	   (<= (abs (- (quot% j) (quot% 2)))
	       (/ (- 1 (expt 8 (- 2 j))) 112)))
  :hints (("Goal" :in-theory (enable quot%) :induct (quot% j))
          ("Subgoal *1/2" :use (rem%-8-bnds-15) :in-theory (disable abs))))

(local-defthmd rem%-8-bnds-17
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(>= j 3))
	   (< (abs (- (quot% j) (quot% 2)))
	      1/112))
  :hints (("Goal" :use (rem%-8-bnds-16) :nonlinearp t)))

(local-defund qmin8 (i)
  (max 1/2 (+ 55/112 (/ i 64))))

(local-defund qmax8 (i)
  (min 1 (+ 57/112 (/ i 64))))

(local-defthmd rem%-8-bnds-18
  (implies (and (= (r%) 8) (= (a%) 4)
                (approx8%-inv 1)
                (approx8%-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3))
	   (and (<= (qmin8 (i8% 2)) (quot% j))
	        (>= (qmax8 (i8% 2)) (quot% j))))
  :hints (("Goal" :use (rem%-8-bnds-6 rem%-8-bnds-17)
                  :in-theory (enable quot%-bnds-inv qmin8 qmax8))))

(local-defthmd rem%-8-bnds-19
  (implies (and (= (r%) 8) (= (a%) 4)
                (approx8%-inv 1)
                (approx8%-inv 2)
		(quot%-bnds-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3)
		(member k '(1 2 3 4)))
	   (and (>= (sel-upper-sqrt (1- k) j)
	           (* 2 (qmin8 (i8% 2)) (- k 3/7)))
		(<= (sel-lower-sqrt k j)
		   (+ (* 2 (qmax8 (i8% 2)) (- k 4/7))
		      (* 1/4096 (- k 4/7) (- k 4/7))))))
  :hints (("Goal" :in-theory (enable rho% sel-lower-sqrt sel-upper-sqrt qmin8 qmax8)
                  :use (rem%-8-bnds-7 rem%-8-bnds-18)
		  :nonlinearp t)))

(local-defthmd rem%-8-bnds-20
  (implies (and (= (r%) 8) (= (a%) 4)
                (approx8%-inv 1)
                (approx8%-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3)
		(member k '(-3 -2 -1 0)))
	   (and (> (sel-upper-sqrt (1- k) j)
	           (* 2 (qmax8 (i8% 2)) (- k 3/7)))
		(<= (sel-lower-sqrt k j)
		   (+ (* 2 (qmin8 (i8% 2)) (- k 4/7))
		      (* 1/4096 (- k 4/7) (- k 4/7))))))
  :hints (("Goal" :in-theory (enable rho% sel-lower-sqrt sel-upper-sqrt qmin8 qmax8)
                  :use (rem%-8-bnds-7 rem%-8-bnds-18)
		  :nonlinearp t)))

(local-defthmd rem%-8-bnds-21
  (implies (and (= (r%) 8) (= (a%) 4)
                (approx8%-inv 1)
                (approx8%-inv 2)
		(quot%-bnds-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3)
		(= (i8% 2) 1))
	  (<= (sel-lower-sqrt -3 j)
	      -5675/1568))
  :hints (("Goal" :in-theory (enable quot% i8% rho% sel-lower-sqrt)
                  :use (rem%-8-bnds-7 rem%-8-bnds-16)
		  :nonlinearp t)))

(local-defthmd rem%-8-bnds-22
  (implies (and (= (r%) 8) (= (a%) 4)
                (approx8%-inv 1)
                (approx8%-inv 2)
		(quot%-bnds-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3)
		(member k '(-3 -2 -1 0 1 2 3 4)))
	   (and (>= (sel-upper-sqrt (1- k) j)
	            (ms8 (i8% 2) j k))
		(<= (+ (sel-lower-sqrt k j) 1/128)
		    (ms8 (i8% 2) j k))))
  :hints (("Goal" :in-theory (enable rho% qmin8 qmax8 ms8)
                  :use (rem%-8-bnds-7 rem%-8-bnds-19 rem%-8-bnds-20 rem%-8-bnds-21)
		  :nonlinearp t)))

(local-defthm i8-j-2
  (implies (and (natp j)
                (>= j 3))
	   (equal (i8% j) (i8% 2)))
  :hints (("Goal" :in-theory (enable quot% i8%) :induct (quot% j))))

(local-defthm rem%-8-bnds-35
  (implies (and (= (r%) 8) (= (a%) 4)
                (approx8%-inv 1)
                (approx8%-inv 2)
		(quot%-bnds-inv 2)
		(quot%-bnds-inv j)
		(natp j)
		(>= j 3))
	   (and (or (= (q% (1+ j)) 4)
	            (<= (ms8 (i8% j) j (1+ (q% (1+ j)))) (sel-upper-sqrt (q% (1+ j)) j)))
	        (or (= (q% (1+ j)) -4)
		    (>= (ms8 (i8% j) j (q% (1+ j))) (+ (sel-lower-sqrt (q% (1+ j)) j) 1/128)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance q%-8-vals (j (1+ j)))
                        (:instance rem%-8-bnds-22 (k (q% (1+ j))))
                        (:instance rem%-8-bnds-22 (k (1+ (q% (1+ j)))))))))

(local-defthmd hyp-inv-8
  (implies (and (natp j)
                (natp k)
		(<= k j)
		(s8-hyp j))
	   (s8-inv k))
  :hints (("Goal" :in-theory (enable s8-hyp) :induct (s8-hyp j))))

(local-defthm rem%-8-bnds-36
  (implies (and (= (r%) 8) (= (a%) 4)
		(natp j)
		(>= j 3)
		(s8-hyp j))
	   (and (or (= (q% (1+ j)) 4)
	            (<= (ms8 (i8% j) j (1+ (q% (1+ j)))) (sel-upper-sqrt (q% (1+ j)) j)))
	        (or (= (q% (1+ j)) -4)
		    (>= (ms8 (i8% j) j (q% (1+ j))) (+ (sel-lower-sqrt (q% (1+ j)) j) 1/128)))))
  :rule-classes ()
  :hints (("Goal" :use (rem%-8-bnds-35
                        (:instance hyp-inv-8 (k j))
                        (:instance hyp-inv-8 (k 1))
                        (:instance hyp-inv-8 (k 2))
                        (:instance hyp-inv-8 (k 3)))
		  :in-theory '(natp s8-inv zp))))

(local-defthm rem%-8-bnds-37
  (implies (natp j)
           (or (= j 0) (= j 1) (= j 2) (>= j 3)))
  :rule-classes ())

(local-defthm rem%-8-bnds-38
  (implies (and (= (r%) 8) (= (a%) 4)
		(or (= j 0) (= j 1) (= j 2))
		(s8-hyp j))
	   (and (or (= (q% (1+ j)) 4)
	            (<= (ms8 (i8% j) j (1+ (q% (1+ j)))) (sel-upper-sqrt (q% (1+ j)) j)))
	        (or (= (q% (1+ j)) -4)
		    (>= (ms8 (i8% j) j (q% (1+ j))) (+ (sel-lower-sqrt (q% (1+ j)) j) 1/128)))))
  :rule-classes ()
  :hints (("Goal" :use (rem%-8-bnds-3 rem%-8-bnds-8 rem%-8-bnds-9)
                  :in-theory '(s8-inv s8-hyp zp))))

(local-defthm rem%-8-bnds-39
  (implies (and (= (r%) 8) (= (a%) 4)
		(natp j)
		(s8-hyp j))
	   (and (or (= (q% (1+ j)) 4)
	            (<= (ms8 (i8% j) j (1+ (q% (1+ j)))) (sel-upper-sqrt (q% (1+ j)) j)))
	        (or (= (q% (1+ j)) -4)
		    (>= (ms8 (i8% j) j (q% (1+ j))) (+ (sel-lower-sqrt (q% (1+ j)) j) 1/128)))))
  :rule-classes ()
  :hints (("Goal" :use (rem%-8-bnds-36 rem%-8-bnds-37 rem%-8-bnds-38)
                  :in-theory (theory 'minimal-theory))))

(local-defthmd rem%-8-bnds-40
  (implies (and (= (r%) 8) (= (a%) 4)
		(rationalp a))
            (let ((k (select-digit-s8 a (i8% 0) 0)))
	      (and (or (= k -4)
	               (>= a (ms8 (i8% 0) 0 k)))
	           (or (= k 4)
		       (< a (ms8 (i8% 0) 0 (1+ k)))))))
  :hints (("Goal" :in-theory (enable ms8 select-digit-s8))))

(local-defthmd rem%-8-bnds-41
  (implies (and (= (r%) 8) (= (a%) 4)
                (s8-hyp 1)
		(rationalp a))
            (let ((k (select-digit-s8 a (i8% 1) 1)))
	      (and (or (= k -4)
	               (>= a (ms8 (i8% 1) 1 k)))
	           (or (= k 4)
		       (< a (ms8 (i8% 1) 1 (1+ k)))))))
  :hints (("Goal" :in-theory (enable ms8 select-digit-s8)
                  :use (rem%-8-bnds-4))))

(local-defthmd rem%-8-bnds-42
  (implies (and (= (r%) 8) (= (a%) 4)
		(natp j)
		(>= j 2)
		(member i (nats 33))
		(rationalp a))
            (let ((k (select-digit-s8 a i j)))
	      (and (or (= k -4)
	               (>= a (ms8 i j k)))
	           (or (= k 4)
		       (< a (ms8 i j (1+ k)))))))
  :hints (("Goal" :in-theory (enable ms8 select-digit-s8))))

(local-defthm rem%-8-bnds-43
  (implies (and (= (r%) 8) (= (a%) 4)
                (s8-hyp j)
		(natp j)
		(>= j 2))
	   (quot%-bnds-inv 2))
  :hints (("Goal" :in-theory (enable s8-hyp))))

(local-defthmd rem%-8-bnds-44
  (implies (and (= (r%) 8) (= (a%) 4)
		(natp j)
		(>= j 2)
		(s8-hyp j)
		(rationalp a))
            (let ((k (select-digit-s8 a (i8% j) j)))
	      (and (or (= k -4)
	               (>= a (ms8 (i8% j) j k)))
	           (or (= k 4)
		       (< a (ms8 (i8% j) j (1+ k)))))))
  :hints (("Goal" :in-theory (disable ms8)
                  :use (rem%-8-bnds-7 i8-j-2 (:instance rem%-8-bnds-42 (i (i8% j)))))))

(local-defthmd rem%-8-bnds-45
  (implies (and (= (r%) 8) (= (a%) 4)
		(natp j)
		(s8-hyp j)
		(rationalp a))
            (let ((k (select-digit-s8 a (i8% j) j)))
	      (and (or (= k -4)
	               (>= a (ms8 (i8% j) j k)))
	           (or (= k 4)
		       (< a (ms8 (i8% j) j (1+ k)))))))
  :hints (("Goal" :use (rem%-8-bnds-40 rem%-8-bnds-41 rem%-8-bnds-44))))

(local-defthmd rem%-8-bnds-46
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(s8-hyp j))
	   (equal (q% (1+ j)) (select-digit-s8 (approx8% j) (i8% j) j)))
  :hints (("Goal" :in-theory (enable s8-hyp s8-inv approx8%-inv))))

(local-defthmd rem%-8-bnds-47
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(s8-hyp j))
	   (and (or (= (q% (1+ j)) -4)
	            (>= (approx8% j) (ms8 (i8% j) j (q% (1+ j)))))
	        (or (= (q% (1+ j)) 4)
		    (< (approx8% j) (ms8 (i8% j) j (1+ (q% (1+ j))))))))
  :hints (("Goal" ;:in-theory (e/d (s8-hyp s8-inv approx8%-inv) (ms8))
                  :use (rem%-8-bnds-46 (:instance rem%-8-bnds-45 (a (approx8% j)))))))

(local-defthmd rem%-8-bnds-48
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(s8-hyp j)
		(approx8%-inv j)
		(or (= j 0)
		    (= (q% (1+ j)) 4)
		    (approx8%-bounds j (1+ (q% (1+ j)))))
		(or (= j 0)
		    (= (q% (1+ j)) -4)
		    (approx8%-bounds j (q% (1+ j)))))
           (and (<= (sel-lower-sqrt (q% (1+ j)) j) (* 8 (rem% j)))
	        (>= (sel-upper-sqrt (q% (1+ j)) j) (* 8 (rem% j)))))
  :hints (("Goal" :in-theory (enable approx8%-bounds)
                  :use (rem%-8-bnds-1 rem%-8-bnds-39 rem%-8-bnds-47))))

(local-defthmd rem%-8-bnds-49
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(s8-hyp j))
           (and (<= (sel-lower-sqrt (q% (1+ j)) j) (* 8 (rem% j)))
	        (>= (sel-upper-sqrt (q% (1+ j)) j) (* 8 (rem% j)))))
  :hints (("Goal" :in-theory (enable s8-hyp s8-inv approx8%-inv)
                  :use (rem%-8-bnds-48 (:instance q%-8-vals (j (1+ j)))))))

(local-defthmd rem%-8-bnds
  (implies (and (= (r%) 8) (= (a%) 4)
                (natp j)
		(s8-hyp j))
           (rem%-bnds-inv (1+ j)))
  :hints (("Goal" :in-theory '(rem%-bnds-inv)
                  :use (rem-sqrt-bnds-next rem%-8-bnds-49))))

(local-defthmd quot8%-bnds-1-1
  (implies (and (= (r%) 8) (= (a%) 4)
		(rationalp a))
           (and (implies (>= a (ms8 (i8% 0) 0 0))
                         (>= (select-digit-s8 a (i8% 0) 0) 0))
		(implies (< a (ms8 (i8% 0) 0 1))
                         (<= (select-digit-s8 a (i8% 0) 0) 0))))
  :hints (("Goal" :in-theory (enable ms8 select-digit-s8))))

(local-defthmd quot8%-bnds-1-2
  (implies (and (= (r%) 8) (= (a%) 4)
                (s8-hyp 1)
		(rationalp a))
           (and (<= (ms8 (i8% 1) 1 0) 0)
	        (> (ms8 (i8% 1) 1 1) 1/128)
		(implies (>= a (ms8 (i8% 1) 1 0))
                         (>= (select-digit-s8 a (i8% 1) 1) 0))
	        (implies (< a (ms8 (i8% 1) 1 1))
                         (<= (select-digit-s8 a (i8% 1) 1) 0))))
  :hints (("Goal" :in-theory (enable ms8 select-digit-s8)
                  :use (rem%-8-bnds-4))))

(local-defthmd quot8%-bnds-1-3
  (implies (and (= (r%) 8) (= (a%) 4)
		(natp j)
		(>= j 2)
		(member i (nats 33))
		(rationalp a))
           (and (<= (ms8 i j 0) 0)
	        (> (ms8 i j 1) 1/128)
		(implies (>= a (ms8 i j 0))
                         (>= (select-digit-s8 a i j) 0))
	        (implies (< a (ms8 i j 1))
                         (<= (select-digit-s8 a i j) 0))))
  :hints (("Goal" :in-theory (enable ms8 select-digit-s8))))

(local-defthmd quot8%-bnds-1-4
  (implies (and (= (r%) 8) (= (a%) 4)
		(natp j)
		(>= j 2)
		(s8-hyp j)
		(rationalp a))
           (and (<= (ms8 (i8% j) j 0) 0)
	        (> (ms8 (i8% j) j 1) 1/128)
		(implies (>= a (ms8 (i8% j) j 0))
                         (>= (select-digit-s8 a (i8% j) j) 0))
	        (implies (< a (ms8 (i8% j) j 1))
                         (<= (select-digit-s8 a (i8% j) j) 0))))
  :hints (("Goal" :in-theory (enable rem%-8-bnds-46)
                  :cases ((= j 2))
                  :use (rem%-8-bnds-7 (:instance quot8%-bnds-1-3 (i (i8% j)))))))

(local-defthmd quot8%-bnds-1-5
  (implies (and (= (r%) 8) (= (a%) 4)
		(natp j)
		(s8-hyp j)
		(rationalp a))
           (and (or (zp j)
	            (and (<= (ms8 (i8% j) j 0) 0)
	                 (> (ms8 (i8% j) j 1) 1/128)))
		(implies (>= a (ms8 (i8% j) j 0))
                         (>= (select-digit-s8 a (i8% j) j) 0))
	        (implies (< a (ms8 (i8% j) j 1))
                         (<= (select-digit-s8 a (i8% j) j) 0))))
  :hints (("Goal" :use (rem%-8-bnds-37 quot8%-bnds-1-1 quot8%-bnds-1-2 quot8%-bnds-1-4))))

(local-defthmd quot8%-bnds-1-6
  (implies (and (= (r%) 8) (= (a%) 4)
		(natp j)
		(s8-hyp j))
	   (and (or (zp j)
	            (and (<= (ms8 (i8% j) j 0) 0)
	                 (> (ms8 (i8% j) j 1) 1/128)))
	        (implies (>= (approx8% j) (ms8 (i8% j) j 0)) (>= (q% (1+ j)) 0))
	        (implies (< (approx8% j) (ms8 (i8% j) j 1)) (<= (q% (1+ j)) 0))))
  :hints (("Goal" :use ((:instance quot8%-bnds-1-5 (a (approx8% j))))
                  :in-theory (enable s8-hyp s8-inv approx8%-inv))))

(in-theory (disable ms8))

(local-defthmd quot8%-bnds-1
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (natp j)
		(s8-hyp j)
		(approx8%-inv j)
		(= (quot% j) 1/2))
	   (>= (quot% (1+ j)) 1/2))
  :hints (("Goal" :in-theory (enable rem% quot% approx8%-inv)
                  :use (x%-constraint quot8%-bnds-1-6)
		  :expand ((approx8%-bounds j 0))
		  :nonlinearp t)))

(local-defthmd quot8%-bnds-2
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (natp j)
		(s8-hyp j)
		(approx8%-inv j)
		(= (quot% j) 1))
	   (<= (quot% (1+ j)) 1))
  :hints (("Goal" :in-theory (enable rem% quot% approx8%-inv)
                  :use (x%-constraint rem%-8-bnds-2 quot8%-bnds-1-6)
		  :expand ((approx8%-bounds j 1))
		  :nonlinearp t)))

(local-defthmd quot8%-bnds-3
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (natp j)
		(s8-hyp j)
		(approx8%-inv j)
		(> (quot% j) 1/2))
	   (> (* (expt 8 j) (quot% j)) (* 1/2 (expt 8 j))))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd quot8%-bnds-4
  (implies (not (zp j))
	   (integerp (* 1/2 (expt 8 j)))))

(local-defthmd quot8%-bnds-5
  (implies (and (integerp a) (integerp b) (> a b))
           (>= a (1+ b))))

(local-defthmd quot8%-bnds-6
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (not (zp j))
		(s8-hyp j)
		(approx8%-inv j)
		(> (quot% j) 1/2))
	   (>= (* (expt 8 j) (quot% j)) (1+ (* 1/2 (expt 8 j)))))
  :hints (("Goal" :use (int-quot-sqrt quot8%-bnds-3 quot8%-bnds-4
                        (:instance quot8%-bnds-5 (a (* (expt 8 j) (quot% j))) (b (* 1/2 (expt 8 j))))))))

(local-defthmd quot8%-bnds-7
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (not (zp j))
		(s8-hyp j)
		(approx8%-inv j)
		(> (quot% j) 1/2))
	   (>= (quot% j) (+ 1/2 (expt 8 (- j)))))
  :hints (("Goal" :use (quot8%-bnds-6)
		  :nonlinearp t)))

(local-defthmd quot8%-bnds-8
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (natp j)
		(s8-hyp j)
		(approx8%-inv j)
		(>= (quot% j) 1/2))
	   (>= (quot% (1+ j)) 1/2))
  :hints (("Goal" :expand ((quot% 0) (quot% 1) (quot% (+ 1 j)))
                  :nonlinearp t
		  :use (quot8%-bnds-1 quot8%-bnds-7 (:instance q%-8-vals (j (1+ j)))))))

(local-defthmd quot8%-bnds-9
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (natp j)
		(s8-hyp j)
		(approx8%-inv j)
		(< (quot% j) 1))
	   (< (* (expt 8 j) (quot% j)) (expt 8 j)))
  :hints (("Goal" :nonlinearp t)))

(local-defthmd quot8%-bnds-10
  (implies (and (integerp a) (integerp b) (< a b))
           (<= a (1- b))))

(local-defthmd quot8%-bnds-11
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (not (zp j))
		(s8-hyp j)
		(approx8%-inv j)
		(< (quot% j) 1))
	   (<= (* (expt 8 j) (quot% j)) (1- (expt 8 j))))
  :hints (("Goal" :use (int-quot-sqrt quot8%-bnds-9
                        (:instance quot8%-bnds-10 (a (* (expt 8 j) (quot% j))) (b (expt 8 j)))))))

(local-defthmd quot8%-bnds-12
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (not (zp j))
		(s8-hyp j)
		(approx8%-inv j)
		(< (quot% j) 1))
	   (<= (quot% j) (- 1 (expt 8 (- j)))))
  :hints (("Goal" :use (quot8%-bnds-11)
		  :nonlinearp t)))

(local-defthmd quot8%-bnds-13
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (natp j)
		(s8-hyp j)
		(approx8%-inv j)
		(<= (quot% j) 1))
	   (<= (quot% (1+ j)) 1))
  :hints (("Goal" :expand ((quot% 0) (quot% 1) (quot% (+ 1 j)))
                  :nonlinearp t
		  :use (quot8%-bnds-2 quot8%-bnds-12 (:instance q%-8-vals (j (1+ j)))))))

(local-defthmd quot8%-bnds
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (natp j)
		(s8-hyp j))
	   (quot%-bnds-inv (1+ j)))
  :hints (("Goal" :in-theory (enable s8-inv quot%-bnds-inv)
		  :use (quot8%-bnds-8 quot8%-bnds-13 (:instance hyp-inv-8 (k j))))))

(defthmd srt-sqrt-rad-8
  (implies (and (= (r%) 8)
                (= (a%) 4)
                (natp j)
		(s8-hyp j))
	   (and (quot%-bnds-inv (1+ j))
                (rem%-bnds-inv (1+ j))))
  :hints (("Goal" :use (rem%-8-bnds quot8%-bnds))))
