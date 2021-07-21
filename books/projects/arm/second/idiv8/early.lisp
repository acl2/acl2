(in-package "RTL")

(include-book "prelim")

(defthmd bvecp-opa
  (bvecp (opa) 64)
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthm natp-opa
  (natp (opa))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthmd bvecp-opb
  (bvecp (opb) 64)
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthm natp-opb
  (natp (opb))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthmd bitp-int32
  (bitp (int32))
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defthmd bitp-sgnd
  (bitp (sgnd))
  :hints (("Goal" :use (input-constraints-lemma)
                  :in-theory (enable input-constraints))))

(defund a () (opval (opa) (int32) (sgnd)))

(defund b () (opval (opb) (int32) (sgnd)))

(defund i () (iquot (a) (b)))

(in-theory (disable (a) (b) (i)))

(defthm int-a
  (integerp (a))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable a opval si))))

(defthm int-b
  (integerp (b))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable b opval si))))

(defthm int-i
  (integerp (i))
  :rule-classes (:type-prescription :rewrite))

(defthmd sgna-a
  (equal (sgna)
         (if (< (a) 0) 1 0))
  :hints (("Goal" :in-theory (enable bitn-bits sgna a opval si)
                  :use (bvecp-opa (:instance bits-bounds (x (opa)) (i 63) (j 32))))))

(defthmd sgnb-b
  (equal (sgnb)
         (if (< (b) 0) 1 0))
  :hints (("Goal" :in-theory (enable bitn-bits sgnb b opval si)
                  :use (bvecp-opb (:instance bits-bounds (x (opb)) (i 63) (j 32))))))

(defthmd sgnq-q
  (implies (and (not (= (a) 0))
                (not (= (b) 0)))
           (equal (sgnq)
                  (if (< (/ (a) (b)) 0) 1 0)))
  :hints (("Goal" :in-theory (enable sgna-a sgnb-b sgnq))))

;;*******************************************************************************

(local-defund cin () (logior1 (sgna) (lognot1 (sgnb))))

(local-defund sum1 ()
  (logxor (bits (lognot (opa)) 63 0)
          (bits (lognot (opb)) 63 0)))

(local-defund car1 ()
  (let ((car0 (bits (ash (logand (bits (lognot (opa)) 63 0)
                                 (bits (lognot (opb)) 63 0))
                         1)
                    63 0)))
    (if1 (int32)
         (setbitn car0 64 32 1)
       (setbitn car0 64 0 1))))

(local-defund arga0 ()
  (bits (if1 (logand1 (sgna) (lognot1 (sgnb)))
             (sum1)
	   (if1 (sgna)
	        (lognot (opa))
	      (opa)))
        63 0))

(local-defund argb0 ()
  (bits (if1 (logand1 (sgna) (lognot1 (sgnb)))
             (car1)
	   (if1 (sgnb)
	        (opb)
              (lognot (opb))))
        63 0))

(local-defund arga ()
  (if1 (int32)
       (setbits (arga0) 64 31 0 0)
     (arga0)))

(local-defund argb ()
  (if1 (int32)
       (setbits (argb0) 64 31 0 4294967295)
     (argb0)))

(local-defund diff () (bits (+ (+ (arga) (argb)) (cin)) 64 0))

(local-defund cmp ()
  (lognot1 (bitn (diff) 64)))

(local-in-theory (disable (cin) (sum1) (car1) (arga0) (argb0) (arga) (argb) (diff) (cmp)))

(local-defthmd compareops-lemma
  (equal (bgta) (cmp))
  :hints (("Goal" :do-not '(preprocess) :expand :lambdas
           :in-theory '(compareops bgta cin sum1 car1 arga0 argb0 arga argb diff cmp))))

(local-defthmd bgta-64-1
  (implies (and (= (int32) 0)
                (< (a) 0)
		(>= (b) 0))
	   (equal (arga)
	          (logxor (bits (lognot (opa)) 63 0)
                          (bits (lognot (opb)) 63 0))))
  :hints (("Goal" :in-theory (enable sgna-a sgnb-b arga arga0 sum1))))

(local-defthmd bgta-64-2
  (implies (and (= (int32) 0)
                (< (a) 0)
		(>= (b) 0))
	   (equal (argb)
	          (1+ (* 2 (bits (logand (bits (lognot (opa)) 63 0)
                                         (bits (lognot (opb)) 63 0))
			         62 0)))))
  :hints (("Goal" :in-theory (enable sgna-a sgnb-b argb argb0 car1))
          ("Goal''" :in-theory (enable cat)
	            :use ((:instance bits-shift-up-1 (k 1) (i 63) (j 1)
		                                     (x (logand (bits (lognot (opa)) 63 0)
                                                                (bits (lognot (opb)) 63 0))))))))

(local-defthmd bgta-64-3
  (implies (and (= (int32) 0)
                (< (a) 0))
	   (equal (bits (lognot (opa)) 63 0)
	          (1- (abs (a)))))
  :hints (("Goal" :in-theory (enable opval si bits-lognot bvecp-opa a sgna)
                  :use (sgna-a))))

(local-defthmd bgta-64-4
  (implies (and (= (int32) 0)
		(>= (b) 0))
	   (equal (bits (lognot (opb)) 63 0)
	          (1- (- (expt 2 64) (abs (b))))))
  :hints (("Goal" :in-theory (enable opval si bits-lognot bvecp-opb b sgnb)
                  :use (sgnb-b))))

(local-defthmd bgta-64-5
  (implies (and (= (int32) 0)
                (< (a) 0)
		(>= (b) 0))
	   (equal (bitn (lognot (opa)) 63)
	          0))
  :hints (("Goal" :in-theory (enable sgna)
                  :use (sgna-a
		        (:instance bitn-lognot (x (opa)) (n 63))
			(:instance bitn-0-1 (x (opa)) (n 63))
			(:instance bitn-0-1 (x (lognot (opa))) (n 63))))))

(local-defthmd bgta-64-6
  (implies (and (= (int32) 0)
                (< (a) 0)
		(>= (b) 0))
	   (equal (argb)
	          (1+ (* 2 (logand (bits (lognot (opa)) 63 0)
                                   (bits (lognot (opb)) 63 0))))))
  :hints (("Goal" :in-theory (enable bgta-64-2 bgta-64-5 bits-logand bitn-logand bitn-bits)
                  :use ((:instance bitn-plus-bits (x (logand (bits (lognot (opa)) 63 0)
                                                             (bits (lognot (opb)) 63 0)))
						  (n 63) (m 0))))))

(local-defthmd bgta-64-7
  (implies (and (= (int32) 0)
                (< (a) 0)
		(>= (b) 0))
	   (equal (+ (arga) (argb))
	          (1+ (+ (bits (lognot (opa)) 63 0)
                         (bits (lognot (opb)) 63 0)))))
  :hints (("Goal" :in-theory (enable bgta-64-1 bgta-64-6)
                  :use ((:instance add-2 (x (bits (lognot (opa)) 63 0))
		                         (y (bits (lognot (opb)) 63 0)))))))

(local-defthmd bgta-64-8
  (implies (and (= (int32) 0)
                (< (a) 0)
		(>= (b) 0))
	   (equal (+ (arga) (argb))
	          (+ (expt 2 64) (abs (a)) (- (abs (b))) -1)))
  :hints (("Goal" :in-theory (enable bgta-64-3 bgta-64-4)
                  :use (bgta-64-7))))

(local-defthmd bgta-64-9
  (and (bvecp (arga) 64)
       (bvecp (argb) 64))
  :hints (("Goal" :in-theory (enable arga0 arga argb0 argb))))

(local-defthmd bgta-64-10
  (equal (diff)
         (+ (arga) (argb) (cin)))
  :hints (("Goal" :in-theory (enable bvecp diff cin sgna-a sgnb-b)
                  :use (bgta-64-9))))

(local-defthmd bgta-64-11
  (implies (and (= (int32) 0)
                (< (a) 0)
		(>= (b) 0))
	   (equal (diff)
	          (+ (expt 2 64) (- (abs (a)) (abs (b))))))
  :hints (("Goal" :in-theory (enable cin sgnb-b sgna-a bgta-64-10)
                  :use (bgta-64-8))))

(local-defthmd bgta-64-12
  (implies (and (= (int32) 0)
                (>= (a) 0))
	   (equal (opa)
	          (abs (a))))
  :hints (("Goal" :in-theory (enable opval si bits-lognot bvecp-opa a sgna)
                  :use (sgna-a))))

(local-defthmd bgta-64-13
  (implies (and (= (int32) 0)
		(< (b) 0))
	   (equal (opb)
	          (- (expt 2 64) (abs (b)))))
  :hints (("Goal" :in-theory (enable opval si bits-lognot bvecp-opb b sgnb)
                  :use (sgnb-b))))

(local-defthmd bgta-64-14
  (implies (and (= (int32) 0)
                (or (< (b) 0) (>= (a) 0)))
	   (and (equal (arga)
	               (if (< (a) 0) (1- (abs (a))) (abs (a))))
		(equal (argb)
		       (if (< (b) 0) (- (expt 2 64) (abs (b))) (1- (- (expt 2 64) (abs (b))))))))		           
  :hints (("Goal" :in-theory (enable sgna-a sgnb-b bgta-64-3 bgta-64-4 bgta-64-13 bgta-64-12 arga arga0 argb argb0)
                  :use (bvecp-opa bvecp-opb))))

(local-defthmd bgta-64-15
  (implies (= (int32) 0)
	   (equal (diff)
	          (+ (expt 2 64) (- (abs (a)) (abs (b))))))
  :hints (("Goal" :in-theory (enable cin sgnb-b sgna-a bgta-64-10 bgta-64-14)
                  :use (bgta-64-11))))

(local-defthmd bgta-64-16
  (bvecp (diff) 65)
  :hints (("Goal" :in-theory (enable diff))))

(local-defthmd bgta-64
  (implies (= (int32) 0)
	   (equal (bgta)
	          (if (> (abs (b)) (abs (a)))
		      1 0)))
  :hints (("Goal" :in-theory (enable compareops-lemma cmp bgta-64-15 bvecp)
                  :use (bgta-64-16
		        (:instance bvecp-bitn-1 (x (diff)) (n 64))))))

(local-defthmd bgta-32-1
  (implies (and (= (int32) 1)
                (< (a) 0)
		(>= (b) 0))
	   (equal (bits (arga) 63 32)
	          (logxor (bits (lognot (opa)) 63 32)
                          (bits (lognot (opb)) 63 32))))
  :hints (("Goal" :in-theory (enable bits-logxor sgna-a sgnb-b arga arga0 sum1))))

(local-defthmd bgta-32-2
  (implies (and (= (int32) 1)
                (< (a) 0)
		(>= (b) 0))
	   (equal (bits (argb) 63 32)
	          (1+ (* 2 (bits (logand (bits (lognot (opa)) 63 32)
                                         (bits (lognot (opb)) 63 32))
			         30 0)))))
  :hints (("Goal" :in-theory (enable sgna-a sgnb-b argb argb0 car1))
          ("Goal''" :in-theory (enable bits-logand cat)
	            :use ((:instance bits-shift-up-1 (k 1) (i 63) (j 33)
		                                     (x (logand (bits (lognot (opa)) 63 0)
                                                                (bits (lognot (opb)) 63 0))))))))

(local-defthmd bgta-32-3
  (implies (and (= (int32) 1)
                (< (a) 0))
	   (equal (bits (lognot (opa)) 63 32)
	          (1- (abs (a)))))
  :hints (("Goal" :in-theory (enable opval si bits-lognot bvecp-opa a sgna)
                  :use (sgna-a))))

(local-defthmd bgta-32-4
  (implies (and (= (int32) 1)
		(>= (b) 0))
	   (equal (bits (lognot (opb)) 63 32)
	          (1- (- (expt 2 32) (abs (b))))))
  :hints (("Goal" :in-theory (enable bitn-bits opval si bits-lognot bvecp-opb b sgnb)
                  :use (sgnb-b))))

(local-defthmd bgta-32-5
  (implies (and (= (int32) 1)
                (< (a) 0)
		(>= (b) 0))
	   (equal (bitn (lognot (opa)) 63)
	          0))
  :hints (("Goal" :in-theory (enable sgna)
                  :use (sgna-a
		        (:instance bitn-lognot (x (opa)) (n 63))
			(:instance bitn-0-1 (x (opa)) (n 63))
			(:instance bitn-0-1 (x (lognot (opa))) (n 63))))))

(local-defthmd bgta-32-6
  (implies (and (= (int32) 1)
                (< (a) 0)
		(>= (b) 0))
	   (equal (bits (argb) 63 32)
	          (1+ (* 2 (logand (bits (lognot (opa)) 63 32)
                                   (bits (lognot (opb)) 63 32))))))
  :hints (("Goal" :in-theory (enable bgta-32-2 bgta-32-5 bits-logand bitn-logand bitn-bits)
                  :use ((:instance bitn-plus-bits (x (logand (bits (lognot (opa)) 63 32)
                                                             (bits (lognot (opb)) 63 32)))
						  (n 31) (m 0))))))

(local-defthmd bgta-32-7
  (implies (and (= (int32) 1)
                (< (a) 0)
		(>= (b) 0))
	   (equal (+ (bits (arga) 63 32) (bits (argb) 63 32))
	          (1+ (+ (bits (lognot (opa)) 63 32)
                         (bits (lognot (opb)) 63 32)))))
  :hints (("Goal" :in-theory (enable bgta-32-1 bgta-32-6)
                  :use ((:instance add-2 (x (bits (lognot (opa)) 63 32))
		                         (y (bits (lognot (opb)) 63 32)))))))

(local-defthmd bgta-32-8
  (implies (and (= (int32) 1)
                (< (a) 0)
		(>= (b) 0))
	   (equal (+ (bits (arga) 63 32) (bits (argb) 63 32))
	          (+ (expt 2 32) (abs (a)) (- (abs (b))) -1)))
  :hints (("Goal" :in-theory (enable bgta-32-3 bgta-32-4)
                  :use (bgta-32-7))))

(local-defthmd bgta-32-9
  (implies (= (int32) 1)
           (and (equal (bits (arga) 31 0) 0)
                (equal (bits (argb) 31 0) (1- (expt 2 32)))))
  :hints (("Goal" :in-theory (enable arga argb))))

(local-defthmd bgta-64-10
  (equal (diff)
         (+ (arga) (argb) (cin)))
  :hints (("Goal" :in-theory (enable bvecp diff cin sgna-a sgnb-b)
                  :use (bgta-32-9))))

(local-defthmd bgta-32-11
  (implies (and (= (int32) 1)
                (< (a) 0)
		(>= (b) 0))
	   (equal (diff)
	          (+ (expt 2 64) (* (expt 2 32) (- (abs (a)) (abs (b)))))))
  :hints (("Goal" :in-theory (enable cin sgnb-b sgna-a bgta-32-9 bgta-64-10)
                  :use (bgta-32-8 bgta-64-9
		        (:instance bits-plus-bits (x (arga)) (n 63) (m 0) (p 32))
			(:instance bits-plus-bits (x (argb)) (n 63) (m 0) (p 32))))))

(local-defthmd bgta-32-12
  (implies (and (= (int32) 1)
                (>= (a) 0))
	   (equal (bits (opa) 63 32)
	          (abs (a))))
  :hints (("Goal" :in-theory (enable opval si bitn-bits bits-lognot bvecp-opa a sgna)
                  :use (sgna-a))))

(local-defthmd bgta-32-13
  (implies (and (= (int32) 1)
		(< (b) 0))
	   (equal (bits (opb) 63 32)
	          (- (expt 2 32) (abs (b)))))
  :hints (("Goal" :in-theory (enable opval si bitn-bits bits-lognot bvecp-opb b sgnb)
                  :use (sgnb-b))))

(local-defthmd bgta-32-14
  (and (bvecp (bits (opa) 63 32) 32)
       (bvecp (bits (lognot (opa)) 63 32) 32)
       (bvecp (bits (lognot (opb)) 63 32) 32)
       (bvecp (bits (opb) 63 32) 32)))

(local-defthmd bgta-32-15
  (implies (and (= (int32) 1)
                (or (< (b) 0) (>= (a) 0)))
	   (and (equal (bits (arga) 63 32)
	               (if (< (a) 0) (1- (abs (a))) (abs (a))))
		(equal (bits (argb) 63 32)
		       (if (< (b) 0) (- (expt 2 32) (abs (b))) (1- (- (expt 2 32) (abs (b))))))))		           
  :hints (("Goal" :in-theory (e/d (sgna-a sgnb-b bgta-32-3 bgta-32-4 bgta-32-13 bgta-32-12 arga arga0 argb argb0)
                                  (bits-bvecp bits-bvecp-simple))
                  :use (bgta-32-14))))

(local-defthmd bgta-32-16
  (implies (= (int32) 1)
	   (equal (diff)
	          (if (= (cin) 1)
		      (+ (expt 2 64) (* (expt 2 32) (- (abs (a)) (abs (b)))))
		    (+ (expt 2 64) (1- (expt 2 32)) (* (expt 2 32) (- (abs (a)) (abs (b))))))))
  :hints (("Goal" :in-theory (enable cin sgnb-b sgna-a bgta-32-9 bgta-64-9 bgta-64-10 bgta-32-15)
                  :use (bgta-32-11
		        (:instance bits-plus-bits (x (arga)) (n 63) (m 0) (p 32))
			(:instance bits-plus-bits (x (argb)) (n 63) (m 0) (p 32))))))

(local-defthmd bgta-32
  (implies (= (int32) 1)
	   (equal (bgta)
	          (if (> (abs (b)) (abs (a)))
		      1 0)))
  :hints (("Goal" :in-theory (enable compareops-lemma cmp bgta-32-16 bvecp)
                  :use (bgta-64-16
		        (:instance bvecp-bitn-1 (x (diff)) (n 64))))))

(defthmd bgta-rewrite
  (equal (bgta)
         (if (> (abs (b)) (abs (a)))
             1 0))
  :hints (("Goal" :use (bgta-64 bgta-32 bitp-int32))))

(defthmd bgta-case
  (implies (> (abs (b)) (abs (a)))
           (equal (data) (bits (i) 63 0)))
  :hints (("Goal" :in-theory (enable iquot cg data i bgta-rewrite)
                  :nonlinearp t)))

;;*******************************************************************************

(defthmd bvecp-mska
  (bvecp (mska) 64)
  :hints (("Goal" :in-theory (enable mska)
                  :use (bvecp-opa))))

(defthmd bvecp-mskb
  (bvecp (mskb) 64)
  :hints (("Goal" :in-theory (enable mskb)
                  :use (bvecp-opb))))

(defthm int-mska
  (integerp (mska))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use bvecp-mska)))

(defthm int-mskb
  (integerp (mskb))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use bvecp-mskb)))

(defund a0 ()
  (if1 (sgnd)
       (si (mska) 64)
     (mska)))

(defund b0 ()
  (if1 (sgnd)
       (si (mskb) 64)
     (mskb)))

(in-theory (disable (a0) (b0)))

(defthmd a0-bounds
  (and (< (a0) (expt 2 64))
       (>= (a0) (- (expt 2 63))))
  :hints (("Goal" :in-theory (enable a0 si)
                  :use (bvecp-mska
		        (:instance bitn-plus-bits (x (mska)) (n 63) (m 0))
			(:instance bits-bounds (x (mska)) (i 62) (j 0))))))

(defthmd b0-bounds
  (and (< (b0) (expt 2 64))
       (>= (b0) (- (expt 2 63))))
  :hints (("Goal" :in-theory (enable b0 si)
                  :use (bvecp-mskb
		        (:instance bitn-plus-bits (x (mskb)) (n 63) (m 0))
			(:instance bits-bounds (x (mskb)) (i 62) (j 0))))))

(defthmd a0-rewrite
  (equal (a0)
         (if1 (int32)
	      (* (expt 2 32) (a))
	    (a)))
  :hints (("Goal" :in-theory (enable a a0 mska opval si bitn-bits cat)
                  :use ((:instance bitn-shift-up (x (bits (opa) 63 32)) (k 32) (n 31))))))

(defthmd b0-rewrite
  (equal (b0)
         (if1 (int32)
	      (* (expt 2 32) (b))
	    (b)))
  :hints (("Goal" :in-theory (enable b b0 mskb opval si bitn-bits cat)
                  :use ((:instance bitn-shift-up (x (bits (opb) 63 32)) (k 32) (n 31))))))

(defthm int-a0
  (integerp (a0))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable a0-rewrite))))

(defthm int-b0
  (integerp (b0))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable b0-rewrite))))

(defthmd i-rewrite
  (equal (i) (iquot (a0) (b0)))
  :hints (("Goal" :in-theory (enable i iquot a0-rewrite b0-rewrite))))

(defthmd sgna-a0
  (equal (sgna)
         (if (< (a0) 0) 1 0))
  :hints (("Goal" :in-theory (enable a0-rewrite sgna-a))))

(defthmd sgnb-b0
  (equal (sgnb)
         (if (< (b0) 0) 1 0))
  :hints (("Goal" :in-theory (enable b0-rewrite sgnb-b))))

(defthmd mska-rewrite
  (equal (mska)
         (if1 (sgna)
	      (- (expt 2 64) (abs (a0)))
	    (abs (a0))))
  :hints (("Goal" :in-theory (enable a0 si bitn-bits sgna-a bvecp) :use (bvecp-mska a0-rewrite))))

(defthmd mskb-rewrite
  (equal (mskb)
         (if1 (sgnb)
	      (- (expt 2 64) (abs (b0)))
	    (abs (b0))))
  :hints (("Goal" :in-theory (enable b0 si bitn-bits sgnb-b bvecp) :use (bvecp-mskb b0-rewrite))))

(defthmd nega-rewrite
  (implies (not (= (a0) 0))
           (equal (nega)
                  (- (expt 2 64) (mska))))
  :hints (("Goal" :in-theory (enable a0 nega lognot bvecp)
                  :use (bvecp-mska
		        (:instance mod-mult (m (- (mska))) (a 1) (n (expt 2 64)))))))

(defthmd negb-rewrite
  (implies (not (= (b0) 0))
           (equal (negb)
                  (- (expt 2 64) (mskb))))
  :hints (("Goal" :in-theory (enable b0 negb lognot bvecp)
                  :use (bvecp-mskb
		        (:instance mod-mult (m (- (mskb))) (a 1) (n (expt 2 64)))))))

(defthmd bvecp-nega
  (bvecp (nega) 64)
  :hints (("Goal" :in-theory (enable nega))))

(defthmd bvecp-negb
  (bvecp (negb) 64)
  :hints (("Goal" :in-theory (enable negb))))

(defthmd bvecp-absa
  (bvecp (absa) 64)
  :hints (("Goal" :in-theory (enable absa))))

(defthmd bvecp-absb
  (bvecp (absb) 64)
  :hints (("Goal" :in-theory (enable absb))))

(defthmd absa-rewrite
  (implies (not (= (a0) 0))
           (equal (absa) (abs (a0))))
  :hints (("Goal" :in-theory (enable absa sgna-a0 nega-rewrite mska-rewrite)
                  :use (bvecp-mska bvecp-nega))))

(defthmd absb-rewrite
  (implies (not (= (b0) 0))
           (equal (absb) (abs (b0))))
  :hints (("Goal" :in-theory (enable absb sgnb-b0 negb-rewrite mskb-rewrite)
                  :use (bvecp-mskb bvecp-negb))))

(defthmd b-0-case
  (implies (= (b) 0)
           (equal (data) 0))
  :hints (("Goal" :in-theory (enable data mskb-rewrite b0-rewrite sgnb-b))))

(defthmd b-mskb-0
  (iff (= (b) 0)
       (= (mskb) 0))
  :hints (("Goal" :in-theory (enable bvecp b0 si)
                  :use (bvecp-mskb b0-rewrite))))

;;*******************************************************************************

(gl::def-gl-rule ispow2-gl-lemma
     :hyp
     (bvecp z 64)
     :concl
     (equal (ispow2-loop-0 0 (mv-nth 1 (mv-list 3 (ispow2-loop-2 0 64 () z))) 1)
            (if (= z (expt 2 (expo z)))
	        1
              0))
     :g-bindings
     '((z (:g-number (0 32 16 48 8 40 24 56 4 36 20 52 12 44 28 60
                      2 34 18 50 10 42 26 58 6 38 22 54 14 46 30 62
		      1 33 17 49 9 41 25 57 5 37 21 53 13 45 29 61
		      3 35 19 51 11 43 27 59 7 39 23 55 15 47 31 63
		      64)))))

(gl::def-gl-rule xor-pow2-cor-gl
     :hyp
     (and (bvecp x 64) (> x 0))
     :concl
     (iff (equal (- (expt 2 64) x)
	         (expt 2 (expo (- (expt 2 64) x))))
	  (equal (bits (logxor (* 2 x) x) 63 0) 
	         (expt 2 (expo (bits (logxor (* 2 x) x) 63 0)))))
     :g-bindings (gl::auto-bindings (:nat x 64)))

(local-defthmd ispow2-pos-with-gl
  (implies (bvecp x 64)
           (equal (ispow2 x 0)
	          (if (= x (expt 2 (expo x)))
		      1
		    0)))
  :hints (("Goal" :in-theory (enable ispow2)
                  :use ((:instance ispow2-gl-lemma (z x))))))

(local-defthmd ispow2-neg-with-gl
  (implies (and (bvecp x 64) (not (= x 0)))
           (equal (ispow2 x 1)
	          (if (= (- (expt 2 64) x)
		         (expt 2 (expo (- (expt 2 64) x))))
		      1
		    0)))
  :hints (("Goal" :in-theory (enable ispow2)
                  :use (xor-pow2-cor-gl (:instance ispow2-gl-lemma (z (bits (logxor (ash x 1) x) 63 0)))))))

(local-defthmd ispow2-sgnb-0
  (implies (= (sgnb) 0)
           (equal (ispow2 (mskb) (sgnb))
	          (if (= (b0) (expt 2 (expo (b0))))
	  	      1 0)))
  :hints (("Goal" :in-theory (enable sgnb-b0 mskb-rewrite)
                  :use (bvecp-mskb (:instance ispow2-pos-with-gl (x (mskb)))))))

(local-defthmd ispow2-sgnb-1
  (implies (= (sgnb) 1)
           (equal (ispow2 (mskb) (sgnb))
	          (if (= (- (b0)) (expt 2 (expo (b0))))
	  	      1 0)))
  :hints (("Goal" :in-theory (enable sgnb-b0 mskb-rewrite)
                  :use (bvecp-mskb b0-bounds
		        (:instance expo-minus (x (b0)))
		        (:instance ispow2-neg-with-gl (x (mskb)))))))

(defthmd ispow2-pow2
  (equal (ispow2 (mskb) (sgnb))
	 (if (or (= (b0) (expt 2 (expo (b0))))
	         (= (b0) (- (expt 2 (expo (b0))))))
	     1 0))
  :hints (("Goal" :in-theory (enable sgnb-b0)
                  :use (ispow2-sgnb-0 ispow2-sgnb-1))))

;;*******************************************************************************

(gl::def-gl-thm clz-expo-with-gl
  :hyp
  (and (bvecp x 64) (> x 0))
  :concl
  (equal (clz64 x) (- 63 (expo x)))
  :g-bindings (gl::auto-bindings (:nat x 64)))

(defthmd clza-rewrite
  (implies (not (= (a) 0))
           (equal (clza) (- 63 (expo (a0)))))
  :hints (("Goal" :in-theory (enable bvecp clza absa-rewrite a0-rewrite)
                  :use (a0-bounds
		        (:instance expo-minus (x (a0)))
		        (:instance clz-expo-with-gl (x (abs (a0))))))))

(defthmd clzb-rewrite
  (implies (not (= (b) 0))
           (equal (clzb) (- 63 (expo (b0)))))
  :hints (("Goal" :in-theory (enable bvecp clzb absb-rewrite b0-rewrite)
                  :use (b0-bounds
		        (:instance expo-minus (x (b0)))
		        (:instance clz-expo-with-gl (x (abs (b0))))))))

;;*******************************************************************************

(local-defthmd ispow2-1
  (and (< (expo (b0)) 64)
       (>= (expo (b0)) 0))
  :hints (("Goal" :use (b0-bounds
                        (:instance expo-monotone (x 1) (y (b0)))
			(:instance expo-monotone (x (b0)) (y (1- (expt 2 64))))))))

(local-defthmd ispow2-2
  (implies (not (= (b) 0))
           (equal (bits (lognot (clzb)) 5 0)
                  (expo (b0))))
  :hints (("Goal" :in-theory (enable bvecp clzb-rewrite bits-lognot)
                  :use (ispow2-1))))

(local-defthmd ispow2-3
  (implies (and (not (= (b) 0))
                (= (bgta) 0)     
                (or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (equal (data)
	          (divpow2 (if1 (sgnb) (nega) (mska)) (sgnq) (expo (b0)))))
  :hints (("Goal" :in-theory (enable mskb-rewrite data sgnb-b0)
                  :use (ispow2-2 bvecp-mska bvecp-nega ispow2-sgnb-0 ispow2-sgnb-1
		        (:instance bits-bounds (x (lognot (clzb))) (i 5) (j 0))))))

(local-defthmd ispow2-4
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 0)
                (or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (equal (data)
	          (divpow2 (abs (a0)) 0 (expo (b0)))))
  :hints (("Goal" :in-theory (enable ispow2-3 sgnq sgna-a0 sgnb-b0 nega-rewrite mska-rewrite))))

(local-defthmd ispow2-5
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 0)
                (or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (equal (data)
	          (bits (i) 63 0)))
  :hints (("Goal" :in-theory (enable ispow2-4 i-rewrite iquot sgnq sgna-a0 sgnb-b0 divpow2))))

(local-defthmd ispow2-6
  (implies (and (not (= (b) 0))
                (= (bgta) 0))
	   (not (equal (a0) 0)))
  :hints (("Goal" :in-theory (enable bgta-rewrite a0-rewrite))))

(local-defthmd ispow2-7
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1)
                (or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (equal (data)
	          (divpow2 (- (expt 2 64) (abs (a0))) 1 (expo (b0)))))
  :hints (("Goal" :in-theory (enable ispow2-3 sgnq sgna-a0 sgnb-b0 nega-rewrite mska-rewrite)
                  :use (ispow2-6))))

(local-defund pada () (bits (ash (- (expt 2 64) (abs (a0))) 64) 127 0))

(local-defund shfta () (bits (ash (si (pada) 128) (- (expo (b0)))) 127 0))

(local-in-theory (disable (pada) (shfta)))

(local-defthmd ispow2-8
  (equal (divpow2 (- (expt 2 64) (abs (a0))) 1 (expo (b0)))
         (if1 (log= (bits (shfta) 63 0) 0)
              (bits (shfta) 127 64)
            (bits (+ (bits (shfta) 127 64) 1) 63 0)))
  :hints (("Goal" :in-theory (enable divpow2 pada shfta))))

(local-defthmd ispow2-9
  (implies (= (sgnq) 1)
           (<= (abs (a0)) (expt 2 63)))
  :hints (("Goal" :in-theory (enable sgnq sgna sgnb si a0)
                  :use (bvecp-mska
		        (:instance bitn-plus-bits (x (mska)) (n 63) (m 0))
			(:instance bits-bounds (x (mska)) (i 62) (j 0))))))

(local-defthmd ispow2-10
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1))
           (equal (si (pada) 128)
	          (- (* (expt 2 64) (abs (a0))))))
  :hints (("Goal" :in-theory (enable si pada bvecp bvecp-bitn-1)
                  :use (ispow2-6 ispow2-9))))

(local-defthmd ispow2-11
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1))
           (equal (shfta)
	          (bits (- (* (expt 2 (- 64 (expo (b0))))
		              (abs (a0))))
			127 0)))
  :hints (("Goal" :in-theory (enable ispow2-10 shfta bvecp)
                  :use (ispow2-1 ispow2-6 ispow2-9))))

(local-defthmd ispow2-12
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1)
                (or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (equal (shfta)
	          (bits (* (expt 2 64) (/ (a0) (b0)))
			127 0)))
  :hints (("Goal" :in-theory (enable ispow2-11 sgnq sgna-a0 sgnb-b0))))

(local-defthmd ispow2-13
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1)
                (or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (integerp (* (expt 2 64) (/ (a0) (b0)))))
  :hints (("Goal" :in-theory (enable sgnq sgna-a0 sgnb-b0)
                  :use (ispow2-1))))

(local-defthmd ispow2-14
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1)
                (or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (equal (bits (shfta) 63 0)
	          (bits (* (expt 2 64) (/ (a0) (b0))) 63 0)))
  :hints (("Goal" :in-theory (enable ispow2-12))))

(local-defthmd ispow2-15
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1)
                (or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (iff (= (bits (shfta) 63 0) 0)
	        (integerp (/ (a0) (b0)))))
  :hints (("Goal" :in-theory (enable ispow2-14 bits-mod)
                  :use (ispow2-13 (:instance mod-0-int (m (* (expt 2 64) (/ (a0) (b0)))) (n (expt 2 64)))))))

(local-defthmd ispow2-16
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1)
                (or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (equal (bits (shfta) 127 64)
	          (bits (fl (/ (a0) (b0))) 63 0)))
  :hints (("Goal" :in-theory (enable ispow2-12)
                  :use ((:instance bits-shift-down-1 (x (* (expt 2 64) (/ (a0) (b0)))) (k 64) (i 63) (j 0))))))

(local-defthmd ispow2-17
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1)
                (integerp (/ (a0) (b0)))
		(or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (equal (data)
	          (bits (i) 63 0)))
  :hints (("Goal" :in-theory (enable cg iquot ispow2-7 ispow2-16 i-rewrite)
                  :use (ispow2-8 ispow2-15))))

(local-defthmd ispow2-18
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (sgnq) 1)
                (not (integerp (/ (a0) (b0))))
		(or (= (b0) (expt 2 (expo (b0))))
		    (= (b0) (- (expt 2 (expo (b0)))))))
           (equal (data)
	          (bits (i) 63 0)))
  :hints (("Goal" :in-theory (enable sgnq sgna-a0 sgnb-b0 iquot ispow2-7 ispow2-16 i-rewrite)
                  :use (ispow2-8 ispow2-15
		        (:instance fl-cg (x (/ (a0) (b0))))))))

(defthmd ispow2-case
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (ispow2 (mskb) (sgnb)) 1))
           (equal (data)
	          (bits (i) 63 0)))
  :hints (("Goal" :in-theory (enable sgnq sgna-a sgnb-b)
                  :use (ispow2-pow2 ispow2-5 ispow2-17 ispow2-18))))

;;*******************************************************************************

(local-defthmd quot-1-1
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (ispow2 (mskb) (sgnb)) 0)
		(= (clza) (clzb)))
           (and (< 0 (abs (b0)))
	        (not (= (a) 0))
	        (<= (abs (b0)) (abs (a0)))))
  :hints (("Goal" :in-theory (enable a0-rewrite b0-rewrite bgta-rewrite)
                  :nonlinearp t)))

(local-defthmd hack-1
  (implies (and (integerp a)
                (integerp b)
		(< 0 (abs b))
		(<= (abs b) (abs a))
		(= (expo a) (expo b)))
	   (and (< (abs (/ a b)) 2)
	        (>= (abs (/ a b)) 1)))
  :hints (("Goal" :nonlinearp t
                  :use ((:instance expo-upper-bound (x a))
		        (:instance expo-lower-bound (x b))))))

(local-defthmd quot-1-2
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (ispow2 (mskb) (sgnb)) 0)
		(= (clza) (clzb)))
           (and (< (abs (/ (a0) (b0))) 2)
	        (>= (abs (/ (a0) (b0))) 1)))
  :hints (("Goal" :in-theory (enable clza-rewrite clzb-rewrite)
                  :nonlinearp t
                  :use (quot-1-1
		        (:instance hack-1 (a (a0)) (b (b0)))))))

(local-defthmd quot-1-3
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (ispow2 (mskb) (sgnb)) 0)
		(= (clza) (clzb)))
           (equal (fl (abs (/ (a0) (b0)))) 1))
  :hints (("Goal" :use (quot-1-2))))

(local-defthmd quot-1-4
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (ispow2 (mskb) (sgnb)) 0)
		(= (clza) (clzb)))
           (equal (i)
	          (if1 (sgnq) -1 1)))
  :hints (("Goal" :use (quot-1-3)
                  :in-theory (enable sgnq sgna-a0 sgnb-b0 cg iquot i-rewrite))))

(defthmd quot-1-case
  (implies (and (not (= (b) 0))
                (= (bgta) 0)
		(= (ispow2 (mskb) (sgnb)) 0)
		(= (clza) (clzb)))
           (equal (data)
	          (bits (i) 63 0)))
  :hints (("Goal" :use (b-mskb-0)
                  :in-theory (enable data quot-1-4))))
		  
;;*******************************************************************************
 (defund earlyp ()
   (or (= (mskb) 0)
       (= (bgta) 1)
       (= (ispow2 (mskb) (sgnb)) 1)
       (= (clza) (clzb))))

(in-theory (disable (earlyp)))

(defthmd early-case
  (implies (earlyp)
           (equal (data)
	          (if (= (b) 0)
		      0
		    (bits (i) 63 0))))
  :hints (("Goal" :in-theory (enable earlyp bgta-rewrite)
           :use (b-0-case b-mskb-0 bgta-case ispow2-case quot-1-case))))

(defthmd b0<=a0
  (implies (not (earlyp))
	   (<= (abs (b0)) (abs (a0))))
  :hints (("Goal" :in-theory (enable earlyp bgta-rewrite a0-rewrite b0-rewrite))))

(defthmd b0<>0
  (implies (not (earlyp))
	   (not (equal (b0) 0)))
  :hints (("Goal" :use (b-mskb-0)
	          :in-theory (enable earlyp b0-rewrite))))

(defthmd clza<=clzb
  (implies (not (earlyp))
	   (< (clza) (clzb)))
  :hints (("Goal" :in-theory (enable earlyp a0-rewrite b0-rewrite clza-rewrite clzb-rewrite)
	   :use (b0<=a0 b0<>0
			(:instance expo-monotone (x (b0)) (y (a0)))))))

(defthmd clza>=0
  (implies (not (earlyp))
	   (natp (clza)))
  :hints (("Goal" :in-theory (enable clza-rewrite)
	   :use (b0<=a0 b0<>0 a0-bounds a0-rewrite
			(:instance expo-monotone (x (a0)) (y (1- (expt 2 64))))))))

(defthmd b0<>1
  (implies (not (earlyp))
	   (not (member (b0) '(1 -1))))
  :hints (("Goal" :in-theory (enable ispow2 earlyp mskb-rewrite sgnb-b0))))

(defthmd clzb<=62
  (implies (not (earlyp))
	   (and (integerp (clzb))
		(<= (clzb) 62)))
  :hints (("Goal" :in-theory (enable clzb-rewrite)
	   :use (b0<>1 b0<>0 b0-bounds b0-rewrite
		       (:instance expo-monotone (y (b0)) (x 2))))))

(defthmd del-bounds
  (implies (not (earlyp))
	   (and (integerp (del))
		(>= (del) 1)
		(<= (del) 62)))
  :hints (("Goal" :in-theory (enable del clza clzb)
	   :use (clza<=clzb clza>=0 clzb<=62))))
