(in-package "RTL")

(include-book "denorm")

(defthmd overflow-1
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (overflow) 1))
           (> (+ (eab) (1- (expt 2 10))) 0))
  :hints (("Goal" :in-theory (enable eab overflow expgtinf expinf expmax)
                  :use (expinc-0-1))))

(defthmd overflow-2
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (overflow) 1))
           (equal (abs (rnd (* (a) (b)) (mode) 53))
	          (* (expt 2 (+ (eab) -52 (exprndinc)))
		     (+ (expt 2 52) (fracrnd)))))
  :hints (("Goal" :in-theory (enable fracrnd)
                  :use (overflow-1 norm-rnd))))

(defthmd overflow-3
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (overflow) 1))
           (>= (abs (rnd (* (a) (b)) (mode) 53))
	       (expt 2 (+ (eab) (exprndinc)))))
  :hints (("Goal" :in-theory (enable overflow-2 fracrnd)
                  :nonlinearp t)))

(in-theory (disable abs))

(defthmd overflow-5
(implies (and (not (specialp))
                (= (hugeposscale) 0)
                (= (overflow) 1))
           (> (abs (rnd (* (a) (b)) (mode) 53))
	      (lpn (dp))))
  :hints (("Goal" :in-theory (enable dp lpn expw bias prec eab overflow expgtinf expinf expmax)
                  :use (overflow-3 expinc-0-1)
                  :nonlinearp t)))

(defthmd overflow-6
  (implies (and (not (specialp))
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (>= (abs (rnd (* (a) (b)) (mode) 53))
	       (expt 2 1024)))
  :hints (("Goal" :in-theory (enable dp lpn expw bias prec)
                  :use ((:instance fp+2 (y (abs (rnd (* (a) (b)) (mode) 53))) (x (lpn (dp))) (n 53))))))

(defthmd overflow-7
  (implies (and (not (specialp))
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (>= (expo (rnd (* (a) (b)) (mode) 53))
	       1024))
  :hints (("Goal" :nonlinearp t
                  :use (overflow-6 (:instance expo-upper-bound (x (rnd (* (a) (b)) (mode) 53)))))))

(defthmd overflow-8
  (implies (and (rationalp x)
                (integerp n)
                (= (abs x) (expt 2 n)))
	   (equal (expo x) n))
  :hints (("Goal" :in-theory (e/d (abs) (expo-minus))
                  :use (expo-minus))))

(defthmd overflow-9
  (implies (and (not (specialp))
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (>= (expo (* (a) (b)))
	       1023))
  :hints (("Goal" :use (overflow-7
                        (:instance overflow-8 (x (rnd (* (a) (b)) (mode) 53)) (n (1+ (expo (* (a) (b))))))
                        (:instance expo-rnd (x (* (a) (b))) (mode (mode)) (n 53))))))

(defthmd overflow-10
  (implies (and (not (specialp))
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (>= (abs (* (a) (b)))
	       (expt 2 1023)))
  :hints (("Goal" :use (overflow-9
                        (:instance expo-lower-bound (x (* (a) (b))))))))

(defthmd overflow-11
  (implies (and (not (specialp))
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (>= (abs (* (a) (b)))
	       (spn (dp))))
  :hints (("Goal" :use (overflow-10) :in-theory (enable dp expw prec bias))))

(defthmd overflow-12
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (> (+ (eab) (1- (expt 2 10))) 0))
  :hints (("Goal" :use (overflow-11 underflow-2 eab-bound))))

(defthmd overflow-13
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (equal (abs (rnd (* (a) (b)) (mode) 53))
	          (* (expt 2 (+ (eab) -52 (exprndinc)))
		     (+ (expt 2 52) (fracrnd)))))
  :hints (("Goal" :in-theory (enable abs fracrnd)
                  :use (overflow-12 norm-rnd))))

(defthmd bvecp-fracrnd
  (bvecp (fracrnd) 52)
  :hints (("Goal" :in-theory (enable fracrnd))))

(defthmd overflow-14
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (equal (expo (abs (rnd (* (a) (b)) (mode) 53)))
	          (+ (eab) (exprndinc))))
  :hints (("Goal" :in-theory (enable bvecp abs)
                  :use (bvecp-fracrnd overflow-13
		        (:instance expo-unique (x (abs (rnd (* (a) (b)) (mode) 53))) (n (+ (eab) (exprndinc)))))
		  :nonlinearp t)))

(defthmd overflow-15
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (>= (+ (eab) (exprndinc))
	       1024))
  :hints (("Goal" :in-theory (enable overflow-7 abs)
                  :use (overflow-14))))

(defthm exprndinc-0-1
  (member (exprndinc) '(0 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exprndinc))))

(defthmd overflow-16
  (implies (and (not (specialp))
                (= (hugeposscale) 0)
                (> (abs (rnd (* (a) (b)) (mode) 53))
	           (lpn (dp))))
           (equal (overflow) 1))
  :hints (("Goal" :in-theory (enable eab overflow expgtinf expinf expmax)
                  :cases ((= (exprndinc) 0))
                  :use (overflow-12 exprndinc-0-1 expinc-0-1 expinc-exprndinc expinc-0-1 overflow-15))))

(defthmd overflow-17
  (implies (and (not (specialp))
                (= (hugeposscale) 0))
           (equal (overflow)
	          (if (> (abs (rnd (* (a) (b)) (mode) 53))
	                 (lpn (dp)))
		      1 0)))
  :hints (("Goal" :in-theory (enable overflow)
           :use (overflow-16 overflow-5))))

(defthmd overflow-18
  (implies (and (not (specialp))
                (= (hugeposscale) 1))
           (equal (overflow) 1))
  :hints (("Goal" :in-theory (enable expgtinf overflow))))

(defthmd overflow-19
  (implies (and (not (specialp))
                (= (hugeposscale) 1))
           (>= (abs (* (a) (b))) (expt 2 1025)))
  :hints (("Goal" :in-theory (enable expgtinf) :use (eab-expgtinf))))

(defthmd overflow-20
  (implies (and (not (specialp))
                (= (hugeposscale) 1))
           (>= (expo (rnd (* (a) (b)) (mode) 53))
               (expo (* (a) (b)))))
  :hints (("Goal" :in-theory (e/d (abs) (expo-2**n expo-minus))
                  :use (common-mode-p-mode
		        (:instance expo-minus (x (rnd (* (a) (b)) (mode) 53)))
			(:instance expo-2**n (n (1+ (expo (* (a) (b))))))
                        (:instance expo-rnd (mode (mode)) (n 53) (x (* (a) (b))))))))

(defthmd overflow-21
  (implies (and (not (specialp))
                (= (hugeposscale) 1))
           (>= (expo (rnd (* (a) (b)) (mode) 53))
               1025))
  :hints (("Goal" :in-theory (enable abs)
                  :use (overflow-19 overflow-20
                        (:instance expo>= (x (abs (* (a) (b)))) (n 1025))))))

(defthmd overflow-22
  (implies (and (not (specialp))
                (= (hugeposscale) 1))
           (>= (abs (rnd (* (a) (b)) (mode) 53))
               (expt 2 1025)))
  :hints (("Goal" :in-theory (enable abs)
                  :use (overflow-21
                        (:instance expo-lower-bound (x (rnd (* (a) (b)) (mode) 53)))))))

(defthmd overflow-23
  (implies (and (not (specialp))
                (= (hugeposscale) 1))
           (> (abs (rnd (* (a) (b)) (mode) 53))
              (lpn (dp))))
  :hints (("Goal" :in-theory (enable lpn dp bias)
                  :use (overflow-22))))

(defthm overflow-hugepos
  (implies (and (not (specialp))
                (<= (abs (rnd (* (a) (b)) (mode) 53))
                    (lpn (dp))))
	   (equal (hugeposscale) 0))
  :hints (("Goal" :in-theory (enable lpn dp bias)
                  :use (overflow-22))))

(defthmd overflow-rewrite
  (implies (not (specialp))
           (equal (overflow)
	          (if (> (abs (rnd (* (a) (b)) (mode) 53))
	                 (lpn (dp)))
		      1 0)))
  :hints (("Goal" :use (overflow-17 overflow-18 overflow-23))))

(defthmd final-1
  (implies (not (specialp))
           (equal (arm-binary-pre-comp-val 'mul (opaz) (opbz) (rz) (dp))
                  ()))
  :hints (("Goal" :in-theory (enable specialp binary-undefined-p)
                  :use (a-class b-class))))

(defthmd final-2
  (implies (not (specialp))
           (equal (arm-binary-pre-comp-excp 'mul (opaz) (opbz) (rz) (dp))
                  (rz)))
  :hints (("Goal" :in-theory (enable specialp binary-undefined-p)
                  :use (a-class b-class))))

(defthmd final-3
  (implies (not (specialp))
           (equal (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
                  (arm-binary-comp 'mul (opaz) (opbz) (rz) (dp))))
  :hints (("Goal" :in-theory (enable arm-binary-spec-rewrite)
                  :use (final-1 final-2))))

(in-theory (disable arm-post-comp (arm-post-comp) arm-binary-spec (arm-binary-spec)))

(defthmd final-4
  (implies (and (not (specialp))
                (= (fscale) 0))
           (and (equal (decode (opaz) (dp)) (a))
	        (equal (decode (opbz) (dp)) (b))))
  :hints (("Goal" :in-theory (enable a b specialp))))

(defthmd final-5
  (implies (and (not (specialp))
                (= (fscale) 0))
           (equal (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
                  (arm-post-comp (* (a) (b)) (rz) (dp))))
  :hints (("Goal" :in-theory (enable binary-eval specialp final-3)
                  :use (final-4 a-nonzero b-nonzero b-class a-class))))

(defthmd final-6
  (implies (not (specialp))
           (equal (fzp) (bitn (rz) 24)))
  :hints (("Goal" :in-theory (enable fzp rz))))

(defthm final-7
  (implies (and (not (specialp))
                (= (fused) 0))
           (and (equal (data) (data-fmul))
	        (equal (flags) (flags-fmul))))
  :hints (("Goal" :in-theory (enable data flags specialp)
                  :use (a-class b-class))))

(defthm final-8
  (equal (bits (rz) 23 22)
         (bits (rin) 23 22))
  :hints (("Goal" :use ((:instance bitn-plus-bits (x (rin)) (n 23) (m 22))
                        (:instance bitn-plus-bits (x (rz)) (n 23) (m 22)))
		  :in-theory (enable b-flags bitn-logior))))

(defthmd final-9
  (implies (and (not (specialp))
                (= (fused) 0)
		(> (abs (rnd (* (a) (b)) (mode) 53))
                   (lpn (dp))))
	   (mv-let (d r) (arm-post-comp (* (a) (b)) (rz) (dp))
	     (and (= d (data))
	          (implies (member b (list (ofc) (ufc) (ixc)))
		           (= (bitn r b) (bitn (logior (rz) (flags)) b))))))
  :hints (("Goal" :in-theory (enable expw dp prec bias data-fmul flags-fmul arm-post-comp overflow-rewrite
                                     sign-rewrite cat bitn-logior modep b-flags mode rmode fpscr-rc nencode sgn)
                  :use ((:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(defthmd final-10
  (implies (and (not (specialp))
                (= (fused) 0)
                (<= (abs (rnd (* (a) (b)) (mode) 53))
                    (lpn (dp)))
		(< (abs (* (a) (b))) (spn (dp)))
		(= (bitn (rin) (fz)) 1))
	   (mv-let (d r) (arm-post-comp (* (a) (b)) (rz) (dp))
	     (and (= d (data))
	          (implies (member b (list (ofc) (ufc) (ixc)))
		           (= (bitn r b) (bitn (logior (rz) (flags)) b))))))
  :hints (("Goal" :in-theory (enable expw dp prec bias data-fmul flags-fmul arm-post-comp overflow-rewrite underflow-rewrite
                                     sign-rewrite cat bitn-logior modep b-flags mode rmode fpscr-rc nencode sgn)
                  :use (final-6 (:instance bvecp-member (x (BITS (RIN) 23 22)) (n 2))))))

(defthmd norm-nencode-1
  (implies (and (not (specialp))
		(= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (abs (rnd (* (a) (b)) (mode) 53))
	          (* (expt 2 (+ (eab) -52 (exprndinc)))
		     (+ (expt 2 52) (fracrnd)))))
  :hints (("Goal" :in-theory (enable abs fracrnd)
                  :use (norm-rnd))))

(defthmd bvecp-fracrnd
  (bvecp (fracrnd) 52)
  :hints (("Goal" :in-theory (enable fracrnd))))

(local-defthmd norm-nencode-2
  (implies (and (not (specialp))
		(= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0))
           (equal (expo (rnd (* (a) (b)) (mode) 53))
	          (+ (eab) (exprndinc))))
  :hints (("Goal" :in-theory (enable bvecp abs)
                  :use (bvecp-fracrnd norm-nencode-1
		        (:instance expo-unique (x (rnd (* (a) (b)) (mode) 53)) (n (+ (eab) (exprndinc)))))
		  :nonlinearp t)))

(local-defthmd norm-nencode-3
  (implies (and (not (specialp))
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (<= (+ (eab) (exprndinc)) 1023))
  :hints (("Goal" :in-theory (enable norm-nencode-2 dp expw prec bias)
                  :use (norm-nencode-1
		        (:instance expo-monotone (x (rnd (* (a) (b)) (mode) 53)) (y (lpn (dp))))))))

(local-defthmd norm-nencode-5
  (implies (and (not (specialp))
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (expgtinf) 0))
  :hints (("Goal" :use (overflow-rewrite)
                  :in-theory (enable overflow))))

(local-defthmd norm-nencode-4
  (implies (and (not (specialp))
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (<= (+ (exp11) (expinc) (exprndinc)) 2046))
  :hints (("Goal" :use (eab-not-expgtinf norm-nencode-5 norm-nencode-3))))

(local-defthmd norm-nencode-6
  (implies (and (not (specialp))
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (abs (rnd (* (a) (b)) (mode) 53))
	          (* (expt 2 (+ (eab) (exprndinc)))
		     (1+ (* (expt 2 -52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable norm-nencode-1))))

(local-defthmd norm-nencode-7
  (implies (and (not (specialp))
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (abs (rnd (* (a) (b)) (mode) 53))
	          (* (expt 2 (+ (exp11) (expinc) -1023 (exprndinc)))
		     (1+ (* (expt 2 -52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable norm-nencode-5 norm-nencode-6)
                  :use (eab-not-expgtinf expinc-0-1))))

(local-defthmd bvecp-exp11
  (bvecp (exp11) 11)
  :hints (("Goal" :in-theory (enable exp11))))

(local-defthmd norm-nencode-8
  (implies (and (not (specialp))
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (<= (exp11) 2046))
  :hints (("Goal" :use (expinc-0-1 norm-nencode-4))))

(local-defthmd norm-nencode-9-1
  (implies (and (not (specialp)) (<= (exp11) 2046)
                (= (hugeposscale) 0)
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (abs (rnd (* (a) (b)) (mode) 53))
	          (* (expt 2 (- (exprnd) 1023))
		     (1+ (* (expt 2 -52) (fracrnd))))))
  :hints (("Goal" :in-theory (enable bvecp exprnd norm-nencode-5 norm-nencode-7)
                  :use (norm-nencode-8 bvecp-exp11 expinc-exprndinc expinc-0-1))))
		  
(local-defthmd norm-nencode-9
  (implies (and (not (specialp))(<= (exp11) 2046)
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (abs (rnd (* (a) (b)) (mode) 53))
	          (* (expt 2 (- (exprnd) 1023))
		     (1+ (* (expt 2 -52) (fracrnd))))))
  :hints (("Goal" :use (norm-nencode-9-1))))

(local-defthmd norm-nencode-10
  (implies (and (not (specialp))
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (abs (rnd (* (a) (b)) (mode) 53))
	          (* (expt 2 (- (exprnd) 1023))
		     (1+ (* (expt 2 -52) (fracrnd))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (norm-nencode-8 norm-nencode-9))))

(defthmd norm-nencode-11
  (implies (and (not (specialp))
                (> (+ (eab) (1- (expt 2 10))) 0)
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (rnd (* (a) (b)) (mode) 53)
	          (if1 (sign)
		       (- (* (expt 2 (- (exprnd) 1023))
		             (1+ (* (expt 2 -52) (fracrnd)))))
	             (* (expt 2 (- (exprnd) 1023))
		        (1+ (* (expt 2 -52) (fracrnd)))))))
  :hints (("Goal" :in-theory (enable sign-rewrite abs)
                  :use (norm-nencode-10))))

(defthmd norm-nencode-12
  (implies (and (not (specialp))
                (>= (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (rnd (* (a) (b)) (mode) 53)
	          (if1 (sign)
		       (- (* (expt 2 (- (exprnd) 1023))
		             (1+ (* (expt 2 -52) (fracrnd)))))
	             (* (expt 2 (- (exprnd) 1023))
		        (1+ (* (expt 2 -52) (fracrnd)))))))
  :hints (("Goal" :use (underflow-2 eab-bound norm-nencode-11))))

(defthmd norm-nencode-13
  (implies (and (not (specialp))
                (>= (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (and (> (exprnd) 0)
	        (<= (exprnd) 2046)))
  :hints (("Goal" :use (underflow-2 overflow-23 expinc-0-1 expinc-exprndinc eab-bound norm-nencode-4 eab-not-expgtinf)
                  :in-theory (enable exprnd bvecp norm-nencode-5))))

(defthmd norm-nencode-14
  (implies (and (not (specialp))
                (= (fused) 0)
                (>= (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (normp (data) (dp)))
  :hints (("Goal" :in-theory (enable encodingp normp underflow-rewrite overflow-rewrite
                              exprnd expw expf dp prec bias data-fmul)
		  :use (norm-nencode-13))))

(defthmd bvecp-exprnd
  (bvecp (exprnd) 11)
  :hints (("Goal" :in-theory (enable exprnd))))

(defthmd norm-nencode-15
  (implies (and (not (specialp))
                (= (fused) 0)
                (>= (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (ndecode (data) (dp))
	          (rnd (* (a) (b)) (mode) 53)))
  :hints (("Goal" :in-theory (enable underflow-rewrite overflow-rewrite abs sgnf norm-nencode-12 sign-rewrite
                              bvecp expf manf norm-nencode-14 expw dp prec bias data-fmul ndecode sgn)
		  :use (bvecp-exprnd bvecp-fracrnd
		        (:instance sgn-rnd (x (* (a) (b))) (mode (mode)) (n 53))
		        (:instance sgn-ndecode (x (data)) (f (dp)))))))

(defthmd norm-nencode
  (implies (and (not (specialp))
                (= (fused) 0)
                (>= (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp))))
           (equal (data)
	          (nencode (rnd (* (a) (b)) (mode) 53) (dp))))
  :hints (("Goal" :use (norm-nencode-14 norm-nencode-15))))

(defthmd final-11
  (implies (and (not (specialp))
                (= (fused) 0)
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
		(>= (abs (* (a) (b))) (spn (dp))))
	   (mv-let (d r) (arm-post-comp (* (a) (b)) (rz) (dp))
	     (and (= d (data))
	          (implies (member b (list (ofc) (ufc) (ixc)))
		           (= (bitn r b) (bitn (logior (rz) (flags)) b))))))
  :hints (("Goal" :in-theory (enable expw dp prec bias norm-nencode flags-fmul arm-post-comp overflow-rewrite underflow-rewrite
                                     bitn-logior modep b-flags mode rmode fpscr-rc)
                  :use (norm-exact underflow-2 eab-bound (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(defthmd drnd-encode-1
  (implies (and (not (specialp))
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (and (equal (exp11) 0)
	        (equal (expinc) 0)))
  :hints (("Goal" :in-theory (enable overflow) :use (eab-not-expgtinf overflow-rewrite expinc-0-1))))

(defthmd drnd-encode-2
  (implies (and (not (specialp))
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
                (= (+ (eab) (1- (expt 2 10))) 0))
	   (equal (exprnd) (exprndinc)))
  :hints (("Goal" :in-theory (enable drnd-encode-1 exprnd))))

(defthmd drnd-encode-3
  (implies (and (not (specialp))
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
                (= (+ (eab) (1- (expt 2 10))) 0)
		(= (drnd (* (a) (b)) (mode) (dp)) 0))
	   (and (equal (exprnd) 0)
	        (equal (fracrnd) 0)))
  :hints (("Goal" :in-theory (enable drnd-encode-2 denorm-drnd-rndup denorm-drnd-no-rndup)
                  :cases ((= (exprndinc) 0)))))

(defthmd drnd-encode-4
  (implies (and (not (specialp))
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
                (= (+ (eab) (1- (expt 2 10))) 0)
		(not (= (drnd (* (a) (b)) (mode) (dp)) 0)))
	   (iff (>= (abs (drnd (* (a) (b)) (mode) (dp))) (expt 2 -1022))
	        (equal (exprndinc) 1)))
  :hints (("Goal" :in-theory (enable bvecp abs denorm-drnd-rndup denorm-drnd-no-rndup)
                  :nonlinearp t
		  :use (bvecp-fracrnd))))

(defthmd drnd-encode-5
  (implies (and (not (specialp))
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
                (= (+ (eab) (1- (expt 2 10))) 0)
		(= (abs (drnd (* (a) (b)) (mode) (dp))) (spn (dp))))
	   (and (equal (exprnd) 1)
	        (equal (fracrnd) 0)))
  :hints (("Goal" :in-theory (enable abs spn dp bias expw drnd-encode-2)
                  :use (drnd-encode-4 denorm-drnd-rndup denorm-drnd-no-rndup))))

(defthmd drnd-encode-6
  (implies (and (not (specialp))
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
                (= (+ (eab) (1- (expt 2 10))) 0)
		(not (= (drnd (* (a) (b)) (mode) (dp)) 0))
		(< (abs (drnd (* (a) (b)) (mode) (dp))) (spn (dp))))
	   (equal (exprnd) 0))
  :hints (("Goal" :in-theory (enable spn dp bias expw drnd-encode-2)
                  :use (drnd-encode-4))))

(defthmd drnd-encode-7
  (implies (and (not (specialp))
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
                (= (+ (eab) (1- (expt 2 10))) 0)
		(not (= (drnd (* (a) (b)) (mode) (dp)) 0))
		(< (abs (drnd (* (a) (b)) (mode) (dp))) (spn (dp))))
	   (not (equal (fracrnd) 0)))
  :hints (("Goal" :in-theory (enable drnd-encode-6 spn dp bias expw drnd-encode-2)
                  :use (denorm-drnd-no-rndup underflow-1 eab-bound drnd-encode-4))))

(defthmd drnd-zencode
  (implies (and (not (specialp))
                (= (fused) 0)
                (< (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
		(= (bitn (rin) (fz)) 0)
		(= (drnd (* (a) (b)) (mode) (dp)) 0))
	   (equal (data)
	          (zencode (if (< (* (a) (b)) 0) 1 0) (dp))))
  :hints (("Goal" :in-theory (enable sign-rewrite overflow-rewrite underflow-rewrite zencode dp sigw expw
                                     final-6 drnd-encode-3 data-fmul)
                  :use (underflow-1 eab-bound))))

(defthmd final-12
  (implies (and (not (specialp))
                (= (fused) 0)
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
		(< (abs (* (a) (b))) (spn (dp)))
		(= (bitn (rin) (fz)) 0)
		(= (drnd (* (a) (b)) (mode) (dp)) 0))
	   (mv-let (d r) (arm-post-comp (* (a) (b)) (rz) (dp))
	     (and (= d (data))
	          (implies (member b (list (ofc) (ufc) (ixc)))
		           (= (bitn r b) (bitn (logior (rz) (flags)) b))))))
  :hints (("Goal" :in-theory (enable expw dp prec bias norm-nencode flags-fmul arm-post-comp overflow-rewrite underflow-rewrite
                                     drnd-zencode bitn-logior modep b-flags mode rmode fpscr-rc)
                  :use (final-6 drnd-equal underflow-1 eab-bound
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(defthmd sgn-drnd
  (implies (and (rationalp x)
                (common-mode-p mode)
                (formatp f)
		(not (= (drnd x mode f) 0)))
	   (equal (sgn (drnd x mode f))
		  (sgn x)))
  :hints (("Goal" :in-theory (enable sgn formatp prec drnd)
                  :use ((:instance sgn-rnd (n (+ (prec f) (expo x) (- (expo (spn f))))))
		        (:instance rnd-choice (n (+ (prec f) (expo x) (- (expo (spn f))))))))))
  
(defthmd drnd-nencode
  (implies (and (not (specialp))
                (= (fused) 0)
                (< (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
		(= (bitn (rin) (fz)) 0)
		(= (abs (drnd (* (a) (b)) (mode) (dp))) (spn (dp))))
	   (equal (data)
	          (nencode (drnd (* (a) (b)) (mode) (dp)) (dp))))
  :hints (("Goal" :in-theory (enable sign-rewrite overflow-rewrite underflow-rewrite zencode dp sigw expw
                                     sgn nencode abs bitn-logior b-flags drnd-encode-5 data-fmul)
                  :use (final-6 underflow-1 eab-bound
		        (:instance sgn-drnd (x (* (a) (b))) (mode (mode)) (f (dp)))
		        (:instance sgn-rnd (x (* (a) (b))) (mode (mode)) (n 53))))))

(defthmd final-13
  (implies (and (not (specialp))
                (= (fused) 0)
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
		(< (abs (* (a) (b))) (spn (dp)))
		(= (bitn (rin) (fz)) 0)
		(= (abs (drnd (* (a) (b)) (mode) (dp))) (spn (dp))))
	   (mv-let (d r) (arm-post-comp (* (a) (b)) (rz) (dp))
	     (and (= d (data))
	          (implies (member b (list (ofc) (ufc) (ixc)))
		           (= (bitn r b) (bitn (logior (rz) (flags)) b))))))
  :hints (("Goal" :in-theory (enable expw dp prec bias drnd-nencode flags-fmul arm-post-comp overflow-rewrite underflow-rewrite
                                     drnd-zencode bitn-logior modep b-flags mode rmode fpscr-rc)
                  :use (final-6 drnd-equal underflow-1 eab-bound
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(defthmd drnd-dencode-1
  (implies (and (not (specialp))
                (= (fused) 0)
                (< (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (* (a) (b)) (mode) (dp)) 0))
		(< (abs (drnd (* (a) (b)) (mode) (dp))) (spn (dp))))
	   (denormp (data) (dp)))
  :hints (("Goal" :in-theory (enable sign-rewrite overflow-rewrite underflow-rewrite zencode dp sigw expw
                                     denormp denorm-drnd-no-rndup sgn dencode abs bitn-logior b-flags
				     sigf expf bvecp encodingp drnd-encode-6 data-fmul)
                  :use (final-6 underflow-1 eab-bound drnd-encode-4 bvecp-fracrnd drnd-encode-7
		        (:instance sgn-drnd (x (* (a) (b))) (mode (mode)) (f (dp)))
		        (:instance sgn-rnd (x (* (a) (b))) (mode (mode)) (n 53))))))

(defthmd drnd-dencode-2
  (implies (and (not (specialp))
                (= (fused) 0)
                (< (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (* (a) (b)) (mode) (dp)) 0))
		(< (abs (drnd (* (a) (b)) (mode) (dp))) (spn (dp))))
	   (equal (ddecode (data) (dp))
	          (drnd (* (a) (b)) (mode) (dp))))
  :hints (("Goal" :in-theory (enable sign-rewrite overflow-rewrite underflow-rewrite zencode dp sigw expw
                                     denormp sgn dencode abs bitn-logior b-flags
				     sgnf ddecode sigf expf bvecp encodingp drnd-encode-6 data-fmul)
                  :use (denorm-drnd-no-rndup final-6 underflow-1 eab-bound drnd-encode-4 bvecp-fracrnd drnd-encode-7
		        (:instance sgn-drnd (x (* (a) (b))) (mode (mode)) (f (dp)))
		        (:instance sgn-rnd (x (* (a) (b))) (mode (mode)) (n 53))))))

(defthmd drnd-dencode
  (implies (and (not (specialp))
                (= (fused) 0)
                (< (abs (* (a) (b))) (spn (dp)))
		(<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (* (a) (b)) (mode) (dp)) 0))
		(< (abs (drnd (* (a) (b)) (mode) (dp))) (spn (dp))))
	   (equal (data)
	          (dencode (drnd (* (a) (b)) (mode) (dp)) (dp))))
  :hints (("Goal" :use (drnd-dencode-1 drnd-dencode-2))))

(defthmd final-14
  (implies (and (not (specialp))
                (= (fused) 0)
                (<= (abs (rnd (* (a) (b)) (mode) 53)) (lpn (dp)))
		(< (abs (* (a) (b))) (spn (dp)))
		(= (bitn (rin) (fz)) 0)
		(not (= (drnd (* (a) (b)) (mode) (dp)) 0))
		(< (abs (drnd (* (a) (b)) (mode) (dp))) (spn (dp))))
	   (mv-let (d r) (arm-post-comp (* (a) (b)) (rz) (dp))
	     (and (= d (data))
	          (implies (member b (list (ofc) (ufc) (ixc)))
		           (= (bitn r b) (bitn (logior (rz) (flags)) b))))))
  :hints (("Goal" :in-theory (enable expw dp prec bias drnd-dencode flags-fmul arm-post-comp overflow-rewrite underflow-rewrite
                                     drnd-zencode bitn-logior modep b-flags mode rmode fpscr-rc)
                  :use (final-6 drnd-equal underflow-1 eab-bound
		        (:instance bvecp-member (x (bits (rin) 23 22)) (n 2))))))

(defthm hack-1
  (implies (and (integerp e)
		(natp c)
		(<= (+ e (expt 2 c)) 1))
	   (<= (expt 2 (1+ e))
	       (expt 2 (- 2 (expt 2 c)))))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t)))

(defthm hack-2
  (IMPLIES (AND (INTEGERP c)
                (RATIONALP X)
                (<= (+ (EXPO X) c) 1))
	 (and (rationalp (abs x))
	      (rationalp (EXPT 2 (+ 1 (EXPO X))))
	      (rationalp (EXPT 2 (+ 2 (- c))))
              (<= (EXPT 2 (+ 1 (EXPO X)))
                  (EXPT 2 (+ 2 (- c))))))
  :rule-classes ()
  :hints (("Goal" :nonlinearp t)))

(defthm hack-3
  (IMPLIES (AND (rationalp u)
                (rationalp v)
		(rationalp w)
		(< u v)
		(<= v w))
	   (< u w))
  :rule-classes ())

(defthm hack-4
  (IMPLIES (AND (< (ABS X) (EXPT 2 (+ 1 (EXPO X))))
                (INTEGERP c)
                (RATIONALP X)
                (<= (+ (EXPO X) c) 1))
           (< (ABS X)
              (EXPT 2 (+ 2 (- c)))))
  :rule-classes ()
  :hints (("Goal" :use (hack-2 (:instance hack-3 (u (abs x)) (v (EXPT 2 (+ 1 (EXPO X)))) (w (EXPT 2 (+ 2 (- c)))))))))

(defthm drepp-bound
  (implies (and (formatp f)
                (rationalp x)
                (drepp x f))
	   (< (abs x) (spn f)))
  :hints (("Goal" :use (expo-upper-bound
                        (:instance hack-4 (c (EXPT 2 (+ -1 (CADDR F))))))
                  :in-theory (enable prec formatp drepp spn expw bias)))
  :rule-classes ())

(defthm drnd-bound
  (implies (and (formatp f)
                (rationalp x)
                (<= (abs x) (spn f))
                (common-mode-p mode))
           (<= (abs (drnd x mode f))
	       (spn f)))
  :hints (("Goal" :use (drnd-exactp-a (:instance drepp-bound (x (drnd x mode f))))
                  :in-theory (enable abs prec formatp sgn drepp spn expw bias)))
  :rule-classes ())

(defthmd final-15
  (implies (and (not (specialp))
                (= (fused) 0))
	   (mv-let (d r) (arm-post-comp (* (a) (b)) (rz) (dp))
	     (and (= d (data))
	          (implies (member b (list (ofc) (ufc) (ixc)))
		           (= (bitn r b) (bitn (logior (rz) (flags)) b))))))
  :hints (("Goal" :use (final-9 final-10 final-11 final-12 final-13 final-14
                        (:instance drnd-bound (x (* (a) (b))) (f (dp)) (mode (mode)))
                        (:instance bitn-0-1 (x (rin)) (n (fz)))))))

(defthmd final-15-a
  (implies (and (not (specialp))
                (= (fused) 0))
	   (mv-let (d r) (arm-post-comp (* (a) (b)) (rz) (dp))
	     (and (= d (data))
	          (implies (member b (list (ofc) (ufc) (ixc)))
		           (= (bitn r b) (bitn (logior (rin) (flags)) b))))))
  :hints (("Goal" :use (final-15)
                  :in-theory (enable rz-flags-b bitn-logior b-flags))))

(defthmd final-16
  (implies (and (not (specialp))
                (= (fused) 0)
                (natp b)
		(not (member b (list (ofc) (ufc) (ixc)))))
	   (equal (bitn (flags) b)
	          (bitn (flags-b) b)))
  :hints (("Goal" :use ((:instance bvecp-member (x b) (n 3)))
                  :in-theory (enable b-flags bvecp bitn-cat bitn-bits flags-fmul))))

(defthmd final-17
  (implies (and (not (specialp))
                (= (fscale) 0)
                (natp b)
		(not (member b (list (ofc) (ufc) (ixc)))))
	   (equal (bitn (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp)))) b)
	          (bitn (logior (rin) (flags-b)) b)))
  :hints (("Goal" :in-theory (enable rz-flags-b final-5 arm-post-comp))))

(defthmd final-18
  (implies (and (not (specialp))
                (= (fused) 0))
	   (bvecp (flags) 8))
  :hints (("Goal" :in-theory (enable b-flags bitn-cat bitn-bits flags-fmul))))

(defthmd final-19
  (implies (and (not (specialp))
                (= (fscale) 0)
                (= (fused) 0)
                (natp b)
		(not (member b (list (ofc) (ufc) (ixc)))))
	   (equal (bitn (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp)))) b)
	          (bitn (logior (rin) (flags)) b)))
  :hints (("Goal" :use (final-16 final-17 final-18) :in-theory (enable b-flags bitn-logior))))

(defthmd final-20
  (implies (and (not (specialp))
                (= (fscale) 0)
                (= (fused) 0))
	   (mv-let (d r) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
	     (and (= d (data))
	          (implies (natp b)
		           (= (bitn r b) (bitn (logior (rin) (flags)) b))))))
  :hints (("Goal" :use (final-5 final-15-a final-19))))

(defthmd final-21
  (implies (and (not (specialp))
                (= (fscale) 0))
	   (integerp (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp))))))
  :hints (("Goal" :in-theory (enable final-5 arm-post-comp))))

(defthmd final-22
  (implies (and (not (specialp))
                (= (fscale) 0)
                (= (fused) 0))
	   (mv-let (d r) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
	     (and (= d (data))
	          (= r (logior (rin) (flags))))))
  :hints (("Goal" :use (final-18 final-21
                        (:instance final-20
                                   (b (bit-diff (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp))))
				                (logior (rin) (flags)))))
			(:instance bit-diff-diff (x (mv-nth 1 (mv-list 2 (arm-binary-spec 'mul (opa) (opb) (rin) (dp)))))
			                         (y (logior (rin) (flags))))))))

(defthmd not-specialp-main
  (implies (and (not (specialp))
                (= (fscale) 0)
                (= (fused) 0))
	   (mv-let (d r) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
	     (and (= d (data))
	          (= r (logior (rin) (flags))))))
  :hints (("Goal" :use (final-21 final-22))))

(defthm fmul64-fmul-main
  (mv-let (data-spec r-spec) (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
    (implies (and (= (fused) 0)
                  (= (fscale) 0))
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec))))
  :hints (("Goal" :use (specialp-main not-specialp-main))))

(defthmd fmul64-fmul-lemma-to-be-functionally-instantiated
  (let ((dnp (bitn (rin) 25))
        (fzp (bitn (rin) 24))
        (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fmul64 (opa) (opb) (scale) fzp dnp rmode 0 0)
      (mv-let (data-spec r-spec)
              (arm-binary-spec 'mul (opa) (opb) (rin) (dp))
	(implies (and (= (fused) 0)
	              (= (fscale) 0))
                 (and (equal data data-spec)
                      (equal (logior (rin) flags) r-spec))))))
  :hints (("Goal" :use (fmul64-fmul-main fmul64-lemma)
                  :in-theory (enable fzp dnp rmode))))

(defmacro ic ()
  '(input-constraints opa opb scale rin 0 0))

(defthm fmul64-fmul-correct
  (implies (input-constraints opa opb scale rin 0 0)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags) (fmul64 opa opb scale fzp dnp rmode 0 0)
               (let ((r (logior rin flags)))         
                 (mv-let (data-spec r-spec)
                         (arm-binary-spec 'mul opa opb rin (dp))
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance fmul64-fmul-lemma-to-be-functionally-instantiated
                         (opa (lambda () (if (ic) opa (opa))))
                         (opb (lambda () (if (ic) opb (opb))))
                         (scale (lambda () (if (ic) scale (scale))))
                         (rin (lambda () (if (ic) rin (rin))))
			 (fused (lambda () (if (ic) 0 (fused))))
			 (fscale (lambda () (if (ic) 0 (fscale))))))
		  :in-theory (disable arm-binary-spec))		  
          ("Subgoal 1" :use (input-constraints-lemma))))



(defthmd final-1-fscale
  (implies (and (not (specialp)) (= (fscale) 1))
           (equal (arm-fscale-spec (opa) (scale) (rin) (dp))
                  (arm-fscale-comp (opaz) (scale) (rz) (dp))))
  :hints (("Goal" :in-theory (enable snanp qnanp specialp arm-fscale-spec-rewrite)
                  :use (a-class))))

(in-theory (disable arm-post-comp (arm-post-comp) arm-fscale-spec (arm-fscale-spec)))

(defthmd final-2-fscale
  (implies (and (not (specialp))
                (= (fscale) 1))
           (equal (decode (opaz) (dp)) (a)))
  :hints (("Goal" :in-theory (enable a specialp))))

(defthmd final-5-fscale
  (implies (and (not (specialp))
                (= (fscale) 1))
           (equal (arm-fscale-spec (opa) (scale) (rin) (dp))
                  (arm-post-comp (* (a) (b)) (rz) (dp))))
  :hints (("Goal" :in-theory (enable expw sigw dp b arm-fscale-comp specialp)
                  :use (a-nonzero a-class final-1-fscale final-2-fscale))))

(defthmd final-17-fscale
  (implies (and (not (specialp))
                (= (fscale) 1)
                (natp b)
		(not (member b (list (ofc) (ufc) (ixc)))))
	   (equal (bitn (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp)))) b)
	          (bitn (logior (rin) (flags-b)) b)))
  :hints (("Goal" :in-theory (enable rz-flags-b final-5-fscale arm-post-comp))))

(defthmd final-18-fscale
  (implies (and (not (specialp))
                (= (fused) 0))
	   (bvecp (flags) 8))
  :hints (("Goal" :in-theory (enable b-flags bitn-cat bitn-bits flags-fmul))))

(defthm fscale-fused
  (implies (= (fscale) 1)
           (equal (fused) 0))
  :hints (("Goal" :in-theory (enable input-constraints) :use (input-constraints-lemma))))

(defthmd final-19-fscale
  (implies (and (not (specialp))
                (= (fscale) 1)
                (natp b)
		(not (member b (list (ofc) (ufc) (ixc)))))
	   (equal (bitn (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp)))) b)
	          (bitn (logior (rin) (flags)) b)))
  :hints (("Goal" :use (final-16 final-17-fscale final-18-fscale) :in-theory (enable b-flags bitn-logior))))

(defthmd final-20-fscale
  (implies (and (not (specialp))
                (= (fscale) 1))
	   (mv-let (d r) (arm-fscale-spec (opa) (scale) (rin) (dp))
	     (and (= d (data))
	          (implies (natp b)
		           (= (bitn r b) (bitn (logior (rin) (flags)) b))))))
  :hints (("Goal" :use (final-5-fscale final-15-a final-19-fscale))))

(defthmd final-21-fscale
  (implies (and (not (specialp))
                (= (fscale) 1))
	   (integerp (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp))))))
  :hints (("Goal" :in-theory (enable final-5-fscale arm-post-comp))))

(defthmd final-22-fscale
  (implies (and (not (specialp))
                (= (fscale) 1))
	   (mv-let (d r) (arm-fscale-spec (opa) (scale) (rin) (dp))
	     (and (= d (data))
	          (= r (logior (rin) (flags))))))
  :hints (("Goal" :use (final-18-fscale final-21-fscale
                        (:instance final-20-fscale
                                   (b (bit-diff (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp))))
				                (logior (rin) (flags)))))
			(:instance bit-diff-diff (x (mv-nth 1 (mv-list 2 (arm-fscale-spec (opa) (scale) (rin) (dp)))))
			                         (y (logior (rin) (flags))))))))

(defthmd not-specialp-fscale
  (implies (and (not (specialp))
                (= (fscale) 1))
	   (mv-let (d r) (arm-fscale-spec (opa) (scale) (rin) (dp))
	     (and (= d (data))
	          (= r (logior (rin) (flags))))))
  :hints (("Goal" :use (final-21-fscale final-22-fscale))))

(defthm fmul64-fscale-main
  (mv-let (data-spec r-spec) (arm-fscale-spec (opa) (scale) (rin) (dp))
    (implies (= (fscale) 1)
             (and (equal (data) data-spec)
                  (equal (logior (rin) (flags)) r-spec))))
  :hints (("Goal" :use (specialp-fscale not-specialp-fscale))))

(defthmd fmul64-fscale-lemma-to-be-functionally-instantiated
  (let ((dnp (bitn (rin) 25))
        (fzp (bitn (rin) 24))
        (rmode (bits (rin) 23 22)))
    (mv-let (data flags) (fmul64 (opa) (opb) (scale) fzp dnp rmode 0 1)
      (mv-let (data-spec r-spec)
              (arm-fscale-spec (opa) (scale) (rin) (dp))
	(implies (= (fscale) 1)
                 (and (equal data data-spec)
                      (equal (logior (rin) flags) r-spec))))))
  :hints (("Goal" :use (fmul64-fscale-main fmul64-lemma)
                  :in-theory (enable fzp dnp rmode))))

(defmacro ic3 ()
  '(input-constraints opa opb scale rin 0 1))

(defthm fmul64-fscale-correct
  (implies (input-constraints opa opb scale rin 0 1)
           (let ((dnp (bitn rin 25))
                 (fzp (bitn rin 24))
                 (rmode (bits rin 23 22)))
             (mv-let (data flags) (fmul64 opa opb scale fzp dnp rmode 0 1)
               (let ((r (logior rin flags)))         
                 (mv-let (data-spec r-spec)
                         (arm-fscale-spec opa scale rin (dp))
                   (and (equal data data-spec)
                        (equal r r-spec)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:functional-instance fmul64-fscale-lemma-to-be-functionally-instantiated
                         (opa (lambda () (if (ic3) opa (opa))))
                         (opb (lambda () (if (ic3) opb (opb))))
                         (scale (lambda () (if (ic3) scale (scale))))
                         (rin (lambda () (if (ic3) rin (rin))))
			 (fused (lambda () (if (ic3) 0 (fused))))
			 (fscale (lambda () (if (ic3) 1 (fscale))))))
		  :in-theory (disable arm-fscale-spec))		  
          ("Subgoal 1" :use (input-constraints-lemma))))


