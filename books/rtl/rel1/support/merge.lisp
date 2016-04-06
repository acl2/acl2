;;; History of this file:
;;; David Russinoff created the original version of this file.  In
;;; 9/99, Matt Kaufmann modified some of the lemmas with an eye toward
;;; increasing the automation provided by this book.  In the process,
;;; some previous stylistic conventions fell by the wayside, such as
;;; disabling :rewrite rules immediate after their statements.

(in-package "ACL2")

(include-book "proofs")

(defthm natp-compound-recognizer
  (equal (natp x)
         (and (integerp x)
              (>= x 0)))
  :rule-classes :compound-recognizer)

(in-theory (disable natp))

; The fpaf3a proof of far-exp-low-lemma-1 in far.lisp requires the
; following to be a :rewrite rule, not just a :type-prescription rule.
; Let's make most or all of our :type-prescription rules into :rewrite
; rules as well.
(defthm natp+
    (implies (and (natp x) (natp y))
	     (natp (+ x y)))
    :rule-classes (:type-prescription :rewrite))

(defthm natp*
    (implies (and (natp x) (natp y))
	     (natp (* x y)))
    :rule-classes (:type-prescription :rewrite))


;;;**********************************************************************
;;;                         REMAINDERS
;;;**********************************************************************

(defthm rem-0
  (implies (natp m)
           (equal (rem m 0) m))
  :hints (("Goal" :expand (rem m 0))))

(defthm rationalp-rem
    (implies (and (rationalp m)
		  (rationalp n))
	     (rationalp (rem m n)))
  :rule-classes :type-prescription)

(defthm rationalp-rem-rewrite
    (implies (and (rationalp m)
		  (rationalp n))
	     (rationalp (rem m n))))

(defthm integerp-rem
    (implies (and (integerp m)
		  (integerp n))
	     (integerp (rem m n)))
  :rule-classes :type-prescription)

(defthm integerp-rem-rewrite
    (implies (and (integerp m)
		  (integerp n))
	     (integerp (rem m n))))

(defthm natp-rem
  (implies (and (natp m)
                (natp n))
           (natp (rem m n)))
  :rule-classes :type-prescription
  :hints (("Goal" :use rem>=0)))

(defthm natp-rem-rewrite
  (implies (and (natp m)
                (natp n))
           (natp (rem m n))))

(defthm rem-bnd-1
    (implies (and (natp m)
		  (natp n)
		  (not (= n 0)))
	     (< (rem m n) n))
  :rule-classes :linear
  :hints (("Goal" :use rem<n)))

(defthm rem-bnd-2
    (implies (and (natp m)
		  (natp n))
	     (<= (rem m n) m))
  :rule-classes :linear
  :hints (("Goal" :use rem<=m)))

(defthm quot-rem
    (implies (and (natp m)
		  (natp n))
	     (equal (+ (* n (fl (/ m n))) (rem m n))
		    m))
  :rule-classes ()
  :hints (("Goal" :use rem-fl)))

(defthm rem-mult
    (implies (and (natp m)
		  (natp a)
		  (natp n))
	     (equal (rem (+ m (* a n)) n)
		    (rem m n)))
  :hints (("Goal" :use rem+)))

(in-theory (disable rem-mult))

(defthm rem-sum
    (implies (and (natp a)
		  (natp b)
		  (natp n))
	     (equal (rem (+ a (rem b n)) n)
		    (rem (+ a b) n)))
  :hints (("Goal" :use rem+rem)))

(in-theory (disable rem-sum))

(defthm rem-diff
    (implies (and (natp a)
		  (natp b)
		  (natp n)
		  (>= a b))
	     (equal (rem (- a (rem b n)) n)
		    (rem (- a b) n)))
  :hints (("Goal" :use rem-minus-rem)))

(in-theory (disable rem-diff))

(defthm rem-equal
    (implies (and (natp m)
		  (natp n)
		  (< m n))
	     (equal (rem m n) m))
  :hints (("Goal" :use (rem<))))

(defthm rem-1
  (implies (natp x)
           (equal (rem x 1) 0))
  :hints (("Goal"
           :use
           ((:instance rem-bnd-1
                       (m x) (n 1))))))

(defthm rem-of-rem
    (implies (and (natp x)
		  (natp a)
		  (natp b)
		  (>= a b))
	     (equal (rem (rem x (expt 2 a)) (expt 2 b))
		    (rem x (expt 2 b))))
  :hints (("Goal" :use (rem-rem))))

(in-theory (disable rem-of-rem))

(defthm rem-must-be-n
    (implies (and (natp m)
		  (natp n)
		  (not (= m 0))
		  (< m (* 2 n))
		  (= (rem m n) 0))
	     (= m n))
  :rule-classes ()
  :hints (("Goal" :use (rem-m=n))))

(defthm rem-prod
    (implies (and (natp m)
		  (natp n)
		  (natp k)
		  (not (= n 0)))
	     (equal (rem (* k m) (* k n))
		    (* k (rem m n))))
  :hints (("Goal" :use (rem**))))

(in-theory (disable rem-prod))

(defthm rem-bnd-3
    (implies (and (natp m)
		  (natp n)
		  (natp a)
		  (natp r)
		  (<= (* a n) m)
		  (< m (+ (* a n) r)))
	     (< (rem m n) r))
  ;; Free variables make this rule very weak, but it seems harmless
  ;; enough to make it a :linear rule.
  :rule-classes :linear
  :hints (("Goal" :use (rem-squeeze))))

(defthm rem-force
    (implies (and (natp m)
		  (natp n)
		  (natp a)
		  (> (* (1+ a) n) m)
		  (>= m (* a n)))
	     (= (rem m n) (- m (* a n))))
  :rule-classes ()
  :hints (("Goal" :use (rem-squeeze-2))))

(defthm rem-equal-int
    (implies (and (natp a)
		  (natp b)
		  (natp n)
		  (= (rem a n) (rem b n)))
	     (integerp (/ (- a b) n)))
  :rule-classes ()
  :hints (("Goal" :use (rem=rem))))

(defthm rem-0-fl
    (implies (and (natp m)
		  (natp n))
	     (iff (= (rem m n) 0)
		  (= m (* (fl (/ m n)) n))))
  :rule-classes ()
  :hints (("Goal" :use (fl-rem-0))))

(defthm quot-bnd
    (implies (and (natp m)
		  (natp n))
	     (>= m (* (fl (/ m n)) n)))
  :rule-classes :linear
  :hints (("Goal" :use (fl-rem-1))))

(defthm rem-0-0
    (implies (and (natp m)
		  (natp n)
		  (natp p)
                  (not (= p 0)))
	     (iff (= (rem m (* n p)) 0)
		  (and (= (rem m n) 0)
		       (= (rem (fl (/ m n)) p) 0))))
  :rule-classes ()
  :hints (("Goal" :use (fl-rem-5))))

(defthm rem-mult-2
    (implies (and (natp n)
		  (natp a))
	     (equal (rem (* a n) n)
		    0))
  :hints (("Goal" :use (divides-rem-0))))

(in-theory (disable rem-mult-2))

(defthm rem-force-equal
    (implies (and (natp a)
		  (natp b)
		  (natp n)
		  (< (abs (- a b)) n)
		  (= (rem a n) (rem b n)))
	     (= a b))
  :rule-classes ()
  :hints (("Goal" :use (rem=rem<n))))

(defthm nk>=k-linear
    (implies (and (integerp n)
		  (integerp k)
		  (not (= n 0)))
	     (>= (abs (* n k)) k))
  :rule-classes :linear
  :hints (("Goal" :use nk>=k)))

(defthm rem-mod-2
    (implies (natp x)
	     (or (= (rem x 2) 0)
		 (= (rem x 2) 1)))
  :rule-classes ()
  :hints (("Goal" :use (rem012))))

(defthm rem-plus-mod-2
    (implies (and (natp x)
		  (natp y))
	     (iff (= (rem (+ x y) 2) (rem x 2))
		  (= (rem y 2) 0)))
  :rule-classes ()
  :hints (("Goal" :use (rem-x-y-x-2))))

(defthm rem-mod-2-not-equal
    (implies (natp x)
	     (not (= (rem x 2) (rem (1+ x) 2))))
  :rule-classes ()
  :hints (("Goal" :use (rem+1-2))))

(defthm x-or-x/2
    (implies (integerp x)
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
  :rule-classes ())

(defthm rem-2*i-rewrite
    (implies (integerp i)
             ;; Rule A3 in fp.lisp suggests using (* 2 i) instead of
             ;; (+ i i).
	     (equal (rem (* 2 i) 2) 0))
    :hints (("Goal" :use rem-2*i)))

(defthm rem-2*i+1
    (implies (integerp i)
	     (not (equal (rem (1+ (* 2 i)) 2) 0)))
  :rule-classes ())

(defthm rem-2*i+1-rewrite
    (implies (natp i)
	     (equal (rem (1+ (* 2 i)) 2) 1))
  :hints (("Goal" :use (rem-2*i+1 (:instance rem-mod-2 (x i))))))

(defun fl-half (x)
  (1- (fl (/ (1+ x) 2))))

(in-theory (disable fl-half))

(defthm fl-half-lemma
    (implies (and (integerp x)
		  (not (integerp (/ x 2))))
	     (= x (1+ (* 2 (fl-half x)))))
  :rule-classes ())


;;;**********************************************************************
;;;                             BITN
;;;**********************************************************************

; Matt K. comment: deleted -- see the comment about April 2016 in
; books/rtl/rel1/support/logdefs.lisp, where natp-bitn is introduced as a
; :type-prescription rule.  It doesn't seem important for this to be a rewrite
; rule.
;(defthm natp-bitn
;    (natp (bitn x n))
;    :rule-classes (:type-prescription :rewrite))

; The following function should often be kept disabled, but we
; leave it enabled while proving the basic lemmas below.
(defun bvecp (x k)
  (and (integerp x)
       (>= x 0)
       (< x (expt 2 k))))

(defthm bvecp-forward
  (implies (bvecp x k)
           (and (integerp x)
                (<= 0 x)
                (< x (expt 2 k))))
  :rule-classes :forward-chaining)

(defthm bitn-rewrite
    ;; !! Perhaps this rule should be disabled by default even if many
    ;; others are kept enabled.
    (implies (and (natp x)
		  (natp k))
	     (equal (bitn x k)
		    (rem (fl (/ x (expt 2 k)))
			 2)))
  :hints (("Goal" :use (bitn-def))))

(in-theory (disable bitn-rewrite))

(defthm bitn-0-0
    (implies (natp k)
	     (equal (bitn 0 k) 0))
  :hints (("Goal" :use (bitn-0))))

(defthm bitn-0-1
    (or (= (bitn x n) 0) (= (bitn x n) 1))
  :rule-classes ())

(defthm bvecp-bitn
    (bvecp (bitn x n) 1)
    :hints (("Goal" :use (bitn-0-1))))

(defthm bitn-rec-0
    (implies (natp x)
	     (equal (bitn x 0)
		    (rem x 2)))
  :hints (("Goal" :use (bitn-alt-0))))

(in-theory (disable bitn-rec-0))

(defthm bitn-rec-pos
    (implies (and (natp x)
		  (natp k)
		  (> k 0))
	     (equal (bitn x k)
		    (bitn (fl (/ x 2)) (1- k))))
  :hints (("Goal" :use (bitn-alt-pos))))

(in-theory (disable bitn-rec-pos))

(defthm bitn-rem-bitn
    (implies (and (natp x)
		  (natp n)
		  (natp k)
		  (> n k))
	     (equal (bitn (rem x (expt 2 n)) k)
		    (bitn x k)))
  :hints (("Goal" :use (bitn-rem))))

(in-theory (disable bitn-rem-bitn))

(defthm bitn-bvecp
    (implies (and (natp n)
		  (bvecp x n))
	     (equal (bitn x n) 0))
  :hints (("Goal" :use (bit-expo-a))))

(in-theory (disable bitn-bvecp))

(defthm bitn-force-1
    (implies (and (natp n)
		  (bvecp x (1+ n))
		  (<= (expt 2 n) x))
	     (equal (bitn x n) 1))
  :hints (("Goal" :use (bit-expo-b))))

(in-theory (disable bitn-force-1))

(defthm bitn-force-2
    (implies (and (bvecp x n) ; bind free var n here
                  (natp n)
		  (natp k)
		  (< k n)
		  (<= (- (expt 2 n) (expt 2 k)) x))
	     (equal (bitn x k) 1))
  :hints (("Goal" :use (bit-expo-c))))

(in-theory (disable bitn-force-2))

(defthm bitn-expt
    (implies (natp n)
	     (equal (bitn (expt 2 n) n) 1))
  :hints (("Goal" :use (bitn-2**n))))

(in-theory (disable bitn-expt))

(defthm bit+expt
    (implies (and (natp x)
		  (natp n))
	     (not (equal (bitn (+ x (expt 2 n)) n)
			 (bitn x n))))
  :rule-classes ()
  :hints (("Goal" :use (bit+-a))))

(defthm bit+expt-2
    (implies (and (natp x)
		  (natp n)
		  (natp m)
		  (> m n))
	     (equal (bitn (+ x (expt 2 m)) n)
		    (bitn x n)))
  :hints (("Goal" :use (bit+-b))))

(in-theory (disable bit+expt-2))

(defthm bitn+mult
    (implies (and (natp x)
		  (natp k)
		  (natp n)
		  (natp m)
		  (> m n))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn x n)))
  :hints (("Goal" :use (bit+*k))))

(in-theory (disable bitn+mult))

(defthm bitn-shift
    (implies (and (natp x)
		  (natp n)
		  (natp k))
	     (= (bitn (* x (expt 2 k)) (+ n k))
		(bitn x n)))
  :rule-classes ()
  :hints (("Goal" :use (bitn-n+k))))

(defthm rem+bitn
    (implies (and (natp a)
		  (natp n))
	     (= (rem a (expt 2 (1+ n)))
		(+ (* (bitn a n) (expt 2 n))
		   (rem a (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use (rem-n+1)
           :in-theory (enable bitn-rec-0))))

(defthm rem-bitn-0
    (implies (and (natp a)
		  (natp n))
	     (iff (= (rem a (expt 2 (1+ n))) 0)
		  (and (= (rem a (expt 2 n)) 0)
		       (= (bitn a n) 0))))
  :rule-classes ()
  :hints (("Goal" :use (rem-n-n+1)
           :in-theory (enable bitn-rec-0))))

(defthm bitn-shift-2
    (implies (and (natp x)
		  (natp k)
		  (natp r))
	     (equal (bitn (fl (/ x (expt 2 r))) k)
		    (bitn x (+ k r))))
  :hints (("Goal" :use (bitn-fl))))

(in-theory (disable bitn-shift-2))

(defthm bitn-shift-3
    (implies (and (natp n)
		  (natp m)
		  (natp k)
		  (bvecp x m)
		  (<= m n))
	     (equal (bitn (+ x (* k (expt 2 m))) n)
		    (bitn k (- n m))))
  :hints (("Goal" :use (bit+*k-2))))

(in-theory (disable bitn-shift-3))


;;;**********************************************************************
;;;                         BITS
;;;**********************************************************************

(defthm rem-bits-equal
    (implies (and (natp x)
		  (natp y)
		  (natp i)
		  (natp j)
		  (= (rem x (expt 2 (1+ i))) (rem y (expt 2 (1+ i)))))
	     (= (bits x i j) (bits y i j)))
  :rule-classes ()
  :hints (("Goal" :use (rem-bits))))

(defthm bits-0-0
    (implies (and (integerp i)
		  (integerp j)
		  (>= i 0))
	     (equal (bits 0 i j) 0))
  :hints (("Goal" :use (bits-0))))

(defthm natp-bits
    (implies (and (natp x)
		  (natp i)
		  (natp j))
	     (natp (bits x i j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (bits-nat))))

(defthm bvecp-bits
    (implies (and (natp x)
		  (natp i)
		  (natp j)
		  (= n (- (1+ i) j)))
	     (bvecp (bits x i j) n))
  :hints (("Goal" :use (bits< bits-nat))))

(defthm bits-tail
    (implies (and (natp n)
		  (bvecp x (1+ n)))
	     (equal (bits x n 0)
		    x)))

(defthm bits-rem
    (implies (and (integerp x)
		  (natp n))
	     (equal (bits x n 0)
		    (rem x (expt 2 (1+ n)))))
  :hints (("Goal" :use (bits-0-rem))))

(in-theory (disable bits-rem))

(defthm bits-shift-1
    (implies (and (natp x)
		  (natp i)
		  (natp j)
		  (natp k))
	     (equal (bits (fl (/ x (expt 2 k)))
			  i
			  j)
		    (bits x (+ i k) (+ j k))))
  :hints (("Goal" :use ((:instance bit-bits-a (i (+ i k)) (j (+ j k)))))))

(in-theory (disable bits-shift-1))

(defthm bits-shift-2
    (implies (and (natp x)
		  (natp i)
		  (natp j)
		  (natp k)
		  (>= i (+ j k)))
	     (equal (bitn (bits x i j) k)
		    (bitn x (+ j k))))
  :hints (("Goal" :use (bit-bits-b))))

(in-theory (disable bits-shift-2))

(defthm bits-shift-3
    (implies (and (natp x)
		  (natp i)
		  (natp j)
		  (natp k)
		  (natp l)
		  (>= i (+ j k)))
	     (equal (bits (bits x i j) k l)
		    (bits x (+ k j) (+ l j))))
  :hints (("Goal" :use (bit-bits-c))))

(in-theory (enable bits-shift-3))

(defthm bits-0-rem-0
    (implies (and (natp x)
		  (natp m)
		  (natp n))
	     (iff (= (rem x (expt 2 (+ m n 1))) 0)
		  (and (= (bits x (+ m n) n) 0)
		       (= (rem x (expt 2 n)) 0))))
  :rule-classes ()
  :hints (("Goal" :use (bits-rem-0))))

(defthm bits-0-bitn-0
    (implies (and (natp x)
		  (natp n)
		  (not (= n 0)))
	     (iff (= (bits x n 0) 0)
		  (and (= (bitn x n) 0)
		       (= (bits x (1- n) 0) 0))))
  :rule-classes ()
  :hints (("Goal" :use (bits-bitn))))

(defthm bits-plus-bits
    (implies (and (natp x)
		  (natp r)
		  (natp n)
		  (natp m)
		  (> n r)
		  (> m n))
	     (= (bits x (1- m) r)
		(+ (bits x (1- n) r)
		   (* (expt 2 (- n r)) (bits x (1- m) n)))))
  :rule-classes ()
  :hints (("Goal" :use (bits-bits))))

(defthm bits-plus-bitn
    (implies (and (natp x)
		  (natp m)
		  (natp n)
		  (> n m))
	     (= (bits x n m)
		(+ (* (bitn x n) (expt 2 (- n m)))
		   (bits x (1- n) m))))
  :rule-classes ()
  :hints (("Goal" :use (bits+bitn))))

(defthm BITS-N-N-rewrite
    (implies (and (natp x)
		  (natp n))
	     (equal (bits x n n)
		    (bitn x n)))
  :hints (("Goal" :in-theory (enable bits-0-rem natp)
		  :use ((:instance bit-bits-a (i n) (j n) (k n))
			(:instance bitn-def (k n))))))

(defthm bitn-plus-bits
    (implies (and (natp x)
		  (natp n)
		  (natp m)
		  (> n m))
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :rule-classes ()
  :hints (("Goal"
           :use (bitn+bits
                 ;; for m=0 case
                 (:instance bits-bits
                            (m (1+ n))
                            (r 0)
                            (n 1))))))

(defthm bits-plus-mult
    (implies (and (natp m)
		  (natp n)
		  (>= n m)
		  (natp k)
		  (<= k m)
		  (natp y)
		  (bvecp x k))
	     (= (bits (+ x (* y (expt 2 k))) n m)
		(bits y (- n k) (- m k))))
  :rule-classes ()
  :hints (("Goal" :use (bits+2**k-2))))


;;;**********************************************************************
;;;                       LOGAND, LOGIOR, and LOGXOR
;;;**********************************************************************

(defthm logand-rewrite
    (implies (and (natp x)
		  (natp y))
	     (equal (logand x y)
		    (+ (* 2 (logand (fl (/ x 2)) (fl (/ y 2))))
		       (logand (rem x 2) (rem y 2)))))
  :rule-classes ((:definition :controller-alist ((binary-logand t t))))
  :hints (("Goal" :use (logand-def))))

(in-theory (disable logand-rewrite))

(defthm natp-logand
    (implies (and (natp i)
		  (natp j))
	     (natp (logand i j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (logand-nat))))

(defthm logand-rem-2
    (implies (and (natp x)
		  (natp y))
	     (equal (rem (logand x y) 2)
		    (logand (rem x 2) (rem y 2))))
  :hints (("Goal" :use (logand-rem))))

(in-theory (disable logand-rem-2))

(defthm logand-fl-2
    (implies (and (natp x)
		  (natp y))
	     (equal (fl (/ (logand x y) 2))
		    (logand (fl (/ x 2)) (fl (/ y 2)))))
  :hints (("Goal" :use (logand-fl))))

(in-theory (disable logand-fl-2))

(defthm logior-rewrite
    (implies (and (natp i)
		  (natp j))
	     (equal (logior i j)
		    (+ (* 2 (logior (fl (/ i 2)) (fl (/ j 2))))
		       (logior (rem i 2) (rem j 2)))))
  :rule-classes ((:definition :controller-alist ((binary-logior t t))))
  :hints (("Goal" :use (logior-def))))

(in-theory (disable logior-rewrite))

(defthm natp-logior
    (implies (and (natp i)
		  (natp j))
	     (natp (logior i j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (logior-nat))))

(defthm logior-rem-2
    (implies (and (natp i)
		  (natp j))
	     (equal (rem (logior i j) 2)
		    (logior (rem i 2) (rem j 2))))
  :hints (("Goal" :use (logior-rem))))

(in-theory (disable logior-rem-2))

(defthm logior-fl-2
    (implies (and (natp i)
		  (natp j))
	     (equal (fl (/ (logior i j) 2))
		    (logior (fl (/ i 2)) (fl (/ j 2)))))
  :hints (("Goal" :use (logior-fl))))

(in-theory (disable logior-fl-2))

(defthm logxor-def-rewrite
    (implies (and (natp x)
		  (natp y))
	     (equal (logxor x y)
		    (+ (* 2 (logxor (fl (/ x 2)) (fl (/ y 2))))
		       (logxor (rem x 2) (rem y 2)))))
  :rule-classes ((:definition :controller-alist ((binary-logxor t t))))
  :hints (("Goal" :use (logxor-def))))

(in-theory (disable logxor-def-rewrite))

(defthm natp-logxor
    (implies (and (natp i)
		  (natp j))
	     (natp (logxor i j)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (logxor-nat))))

(defthm logxor-rem-2
    (implies (and (natp i)
		  (natp j))
	     (equal (rem (logxor i j) 2)
		    (logxor (rem i 2) (rem j 2))))
  :hints (("Goal" :use (logxor-rem))))

(in-theory (disable logxor-rem-2))

(defthm logxor-fl-2
    (implies (and (natp i)
		  (natp j))
	     (equal (fl (/ (logxor i j) 2))
		    (logxor (fl (/ i 2)) (fl (/ j 2)))))
  :hints (("Goal" :use (logxor-fl))))

(in-theory (disable logxor-fl-2))

(defthm logxor-rewrite-2
    ;; !! Do we really want to get rid of logxor?
    (implies (and (bvecp x n)
		  (bvecp y n)
                  (natp n)
		  (not (= n 0)))
	     (equal (logxor x y)
		    (logior (logand x (comp1 y n))
			    (logand y (comp1 x n)))))
  :hints (("Goal" :use (logxor-rewrite))))

(in-theory (disable logxor-rewrite-2))

(defthm logand-0-y
    (equal (logand 0 y) 0))

(defthm logand-x-0
    (equal (logand x 0) 0))

(defthm logxor-0-y
    (implies (integerp y)
	     (equal (logxor 0 y) y)))

(defthm logxor-x-0
    (implies (integerp x)
	     (equal (logxor x 0) x)))

(defthm logxor-self
    (implies (natp x)
	     (equal (logxor x x) 0)))

(defthm logand-ones
    (implies (and (natp n)
		  (bvecp x n))
	     (equal (logand x (1- (expt 2 n)))
		    x))
  :hints (("Goal" :use (logand-2**n-1))))

(in-theory (disable logand-ones))

(defthm logand-commutative
    (implies (and (integerp x)
		  (integerp y))
	     (equal (logand x y) (logand y x)))
  :hints (("Goal" :use (bit-basic-c))))

(defthm logior-commutative
    (implies (and (integerp x)
		  (integerp y))
	     (equal (logior x y) (logior y x)))
  :hints (("Goal" :use (bit-basic-d))))

(defthm logxor-commutative-rewrite
    (implies (and (integerp x)
		  (integerp y))
	     (equal (logxor x y) (logxor y x)))
    :hints (("Goal" :use logxor-commutative)))

(defthm logand-associative
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logand (logand x y) z)
		    (logand x (logand y z))))
  :hints (("Goal" :use (bit-basic-e))))

(in-theory (disable logand-associative))

(defthm logior-associative
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logior (logior x y) z)
		    (logior x (logior y z))))
  :hints (("Goal" :use (bit-basic-f))))

(in-theory (disable logior-associative))

(defthm logxor-associative
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logxor (logxor x y) z)
		    (logxor x (logxor y z))))
  :hints (("Goal" :use (logxor-assoc))))

(in-theory (disable logxor-associative))

(defthm logior-logand
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logior x (logand y z))
		    (logand (logior x y) (logior x z))))
  :hints (("Goal" :use (bit-basic-g))))

(in-theory (disable logior-logand))

(defthm logand-logior
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logand x (logior y z))
		    (logior (logand x y) (logand x z))))
  :hints (("Goal" :use (bit-basic-h))))

(in-theory (disable logand-logior))

(defthm logior-logand-2
    (implies (and (natp x)
		  (natp y)
		  (natp z))
	     (equal (logand  (logior y z) x)
		    (logior (logand y x) (logand z x))))
  :hints (("Goal" :use (bit-basic-h-2))))

(in-theory (disable logior-logand-2))

(defthm logand-self
    (implies (natp x)
	     (equal (logand x x) x))
  :hints (("Goal" :use (logand-x-x))))

(defthm bvecp-logior
    (implies (and (natp n)
		  (bvecp x n)
		  (bvecp y n))
	     (bvecp (logior x y) n))
  :hints (("Goal" :use (or-dist-a natp-logior))))

(defthm logior-expt
    (implies (and (natp n)
		  (natp x)
		  (bvecp y n))
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x) y)))
  :rule-classes ()
  :hints (("Goal" :use (or-dist-b))))

(defthm logior-expt-2
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (= (logior (* (expt 2 n) x)
			(* (expt 2 n) y))
		(* (expt 2 n) (logior x y))))
  :rule-classes ()
  :hints (("Goal" :use (or-dist-c))))

(defthm rem-logior
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (rem (logior x y) (expt 2 n))
		    (logior (rem x (expt 2 n)) (rem y (expt 2 n)))))
  :hints (("Goal" :use (or-dist-d))))

(in-theory (disable rem-logior))

(defthm logand-bnd
    (implies (and (natp x)
		  (natp y))
	     (<= (logand x y) x))
  :rule-classes :linear
  :hints (("Goal" :use (and-dist-a))))

(defthm bvecp-logand
    (implies (and (natp n)
		  (bvecp x n)
		  (natp y))
	     (bvecp (logand x y) n))
  :hints (("Goal" :use (natp-logand logand-bnd))))

(defthm logand-expt
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (= (logand (* (expt 2 n) x) y)
		(* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
  :rule-classes ()
  :hints (("Goal" :use (and-dist-b))))

(defthm rem-logand-expt
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (= (rem (logand x y) (expt 2 n))
		(logand (rem x (expt 2 n)) y)))
  :rule-classes ()
  :hints (("Goal" :use (and-dist-c))))

(defthm rem-logand-rewrite
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (rem (logand x y) (expt 2 n))
		    (logand (rem x (expt 2 n)) (rem y (expt 2 n)))))
  :hints (("Goal" :use (rem-logand))))

(in-theory (disable rem-logand-rewrite))

(local
 (defthm rem-logxor-0
   (implies (and (natp x)
                 (natp y)
                 (equal n 0))
            (equal (rem (logxor x y) (expt 2 n))
                   (logxor (rem x (expt 2 n))
                           (rem y (expt 2 n)))))
   :rule-classes nil
   :hints (("Goal" :use (rem-logxor)))))

(defthm rem-logxor-rewrite
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (rem (logxor x y) (expt 2 n))
		    (logxor (rem x (expt 2 n))
			    (rem y (expt 2 n)))))
  :hints (("Goal" :use (rem-logxor
                        rem-logxor-0
                        (:theorem
                         (implies (and (natp n) (< n 1))
                                  (equal n 0)))))))

(in-theory (disable rem-logxor-rewrite))

(defthm logand-rem-expt
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (< x (expt 2 n)))
	     (= (logand x y)
		(logand x (rem y (expt 2 n)))))
  :rule-classes ()
  :hints (("Goal" :use (and-dist-d))))

(defthm bvecp-logxor
    (implies (and (natp n)
		  (bvecp x n)
		  (bvecp y n))
	     (bvecp (logxor x y) n))
  :hints (("Goal" :use (logxor<2**n
			(:instance logxor-nat (i x) (j y))))))

(defthm bitn-logand
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (bitn (logand x y) n)
		    (logand (bitn x n) (bitn y n))))
  :hints (("Goal" :use (bit-dist-a))))

(in-theory (disable bitn-logand))

(defthm bitn-logior
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (bitn (logior x y) n)
		    (logior (bitn x n) (bitn y n))))
  :hints (("Goal" :use (bit-dist-b))))

(in-theory (disable bitn-logior))

(defthm logxor-bitn
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (equal (bitn (logxor x y) n)
		    (logxor (bitn x n) (bitn y n))))
  :hints (("Goal" :use (bitn-logxor))))

(in-theory (disable logxor-bitn))

(defthm logand-expt-2
    (implies (and (natp x)
		  (natp k))
	     (= (logand x (expt 2 k))
		(* (expt 2 k) (bitn x k))))
  :rule-classes ()
  :hints (("Goal" :use (and-bits-a))))

(defthm logior-expt-3
    (implies (and (natp x)
		  (natp k))
	     (= (logior x (expt 2 k))
		(+ x
		   (* (expt 2 k)
		      (- 1 (bitn x k))))))
  :rule-classes ()
  :hints (("Goal" :use (and-bits-b))))

(defthm logand-expt-3
    (implies (and (natp x)
		  (natp n)
		  (natp k)
		  (< k n))
	     (= (logand x (- (expt 2 n) (expt 2 k)))
		(* (expt 2 k) (bits x (1- n) k))))
  :rule-classes ()
  :hints (("Goal" :use (and-bits-c))))

(defthm logand-expt-4
    (implies (and (natp n)
		  (natp k)
		  (natp l)
		  (< l k)
		  (<= k n))
	     (= (logand (- (1- (expt 2 n)) (expt 2 l)) (- (expt 2 n) (expt 2 k)))
		(- (expt 2 n) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use (and-bits-e))))

(defthm bitn-logxor-0
    (implies (and (natp a)
		  (natp b))
	     (= (bitn (+ a b) 0)
		(bitn (logxor a b) 0)))
  :rule-classes ()
  :hints (("Goal" :use (bitn-0-logxor-+))))


;;;**********************************************************************
;;;                            COMP1
;;;**********************************************************************

(defthm integerp-comp1-nat
    (implies (and (integerp x)
		  (natp n))
	     (integerp (comp1 x n)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use (integerp-comp1))))

(defthm comp1-comp1-rewrite
    (implies (and (integerp n)
		  (integerp x))
	     (equal (comp1 (comp1 x n) n)
                    x))
  :hints (("Goal" :use comp1-comp1)))

(defthm comp1-fl
    (implies (and (natp n)
		  (natp k)
		  (<= k n)
		  (bvecp x n))
	     (= (fl (/ (comp1 x n) (expt 2 k)))
		(comp1 (fl (/ x (expt 2 k))) (- n k))))
  :rule-classes ()
  :hints (("Goal" :use (fl-comp1))))

(defthm rem-comp1-2
    (implies (and (natp n)
		  (not (= n 0))
		  (bvecp x n))
	     (not (= (rem (comp1 x n) 2)
		     (rem x 2))))
  :rule-classes ()
  :hints (("Goal" :use (rem-comp1))))

(defthm bvecp-comp1
    (implies (and (natp n)
		  (bvecp x n))
	     (bvecp (comp1 x n) n))
  :hints (("Goal" :use (comp1-bnds))))

(defthm bitn-comp1-not-equal
    (implies (and (natp n)
		  (bvecp x n)
		  (natp k)
		  (< k n))
	     (not (= (bitn (comp1 x n) k)
		     (bitn x k))))
  :rule-classes ()
  :hints (("Goal" :use (bitn-comp1))))

(defthm rem-comp1-rewrite
    (implies (and (natp n)
		  (natp m)
		  (bvecp x m)
		  (not (= n 0))
		  (>= m n))
	     (equal (rem (comp1 x m) (expt 2 n))
		    (comp1 (rem x (expt 2 n)) n)))
  :hints (("Goal" :use (comp1-rem))))

(in-theory (disable rem-comp1-rewrite))


;;**********************************************************************
;;                        NEW STUFF
;;**********************************************************************

(defthm logior-not-0
    (implies (and (natp x)
		  (natp y)
		  (= (logior x y) 0))
	     (and (= x 0) (= y 0)))
  :rule-classes ()
  :hints (("Goal"
           :expand ((natp x) (natp y))
           :use (expo-upper-bound
                 expo-lower-bound
                 bit-basic-d
                 (:instance bit-basic-b (x y))
                 (:instance expo>= (n 0))
                 (:instance bitn-0-1 (n (expo x)) (x y))
                 (:instance bit-dist-b (n (expo x)))
                 (:instance bit-expo-b (n (expo x)))))))

(defun ls-induct (k x)
  (if (zp k)
      x
    (ls-induct (1- k) (fl (/ x 2)))))

(local-defthm lshiftamt-low-3-1
    (implies (and (integerp k) (> k 0))
	     (= (fl (/ (1- (expt 2 k)) 2))
		(1- (expt 2 (1- k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-unique
                                   (x (/ (1- (expt 2 k)) 2))
                                   (n (1- (expt 2 (1- k)))))))))

(local-defthm lshiftamt-low-3-2
    (implies (and (integerp k) (> k 0))
	     (= (rem (1- (expt 2 k)) 2) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rem012 (x (1- (expt 2 k))))
			(:instance rem+1-2 (x (1- (expt 2 k))))
			(:instance rem-2*i (i (expt 2 (1- k))))))))

(local-defthm lshiftamt-low-3
    (implies (and (integerp k) (>= k 0)
		  (integerp x) (>= x 0) (< x (expt 2 k)))
	     (= (logior (1- (expt 2 k)) x)
		(1- (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :induct (ls-induct k x))
	  ("Subgoal *1/2" :use (lshiftamt-low-3-1
				lshiftamt-low-3-2
				rem012
				(:instance rem-fl (m x) (n 2))
				(:instance rem-fl (m (logior (1- (expt 2 k)) x)) (n 2))
				(:instance logior-nat (i (1- (expt 2 k))) (j x))
				(:instance fl-def (x (/ x 2)))
				(:instance logior-fl (i (1- (expt 2 k))) (j x))
				(:instance logior-rem (i (1- (expt 2 k))) (j x))))))

(local-defthm lshiftamt-low-4
    (implies (and (integerp k) (>= k 0)
		  (integerp x) (> x 0)
		  (= (expo x) k))
	     (= (logior x (1- (expt 2 k)))
		(1- (expt 2 (1+ k)))))
  :rule-classes ()
  :hints (("Goal" :use (expo-upper-bound
			expo-lower-bound
			(:instance expt-pos (x k))
			(:instance integerp-expt (n k))
			(:instance bit-basic-d (x (- x (expt 2 k))) (y (1- (expt 2 k))))
			(:instance or-dist-b (n k) (x 1) (y (- x (expt 2 k))))
			(:instance bit-basic-f (x (expt 2 k)) (y (- x (expt 2 k))) (z (1- (expt 2 k))))
			(:instance lshiftamt-low-3 (x (- x (expt 2 k))))
			(:instance or-dist-b (n k) (x 1) (y (1- (expt 2 k))))))))

(defthm logior-x-0
    (implies (natp x)
	     (equal (logior x 0) x))
  :hints (("Goal" :use (bit-basic-b))))

(local-defthm logior-bits-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(logior (+ (* (expt 2 j) (bits x i j))
			   (bits x (1- j) 0))
			(+ (* (expt 2 j) (bits y i j))
			   (bits y (1- j) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use ((:instance or-dist-d (n (1+ i)))
			(:instance expo+ (m 1) (n i))
			(:instance bits-bits (m (1+ i)) (n j) (r 0))
			(:instance bits-bits (x y) (m (1+ i)) (n j) (r 0))))))

(local-defthm logior-bits-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(logior (logior (* (expt 2 j) (bits x i j))
				(bits x (1- j) 0))
			(logior (* (expt 2 j) (bits y i j))
				(bits y (1- j) 0)))))
  :rule-classes ()
  :hints (("Goal"
           ;; The following theory hint was necessary here, though not
           ;; in Russinoff's earlier version.
           :in-theory (disable natp-bits)
           :use (logior-bits-1
                 bits-nat
                 (:instance bits-nat (x y))
                 (:instance bits-nat (i (1- j)) (j 0))
                 (:instance bits< (i (1- j)) (j 0))
                 (:instance bits-nat (x y) (i (1- j)) (j 0))
                 (:instance bits< (x y) (i (1- j)) (j 0))
                 (:instance or-dist-b (x (bits x i j)) (n j) (y (bits x (1- j) 0)))
                 (:instance or-dist-b (x (bits y i j)) (n j) (y (bits y (1- j) 0)))))))

(local-defthm logior-bits-3
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp c) (>= c 0)
		  (integerp d) (>= d 0))
	     (= (logior (logior a b) (logior c d))
		(logior (logior a c) (logior b d))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-basic-f (x a) (y b) (z (logior c d)))
			(:instance bit-basic-f (x b) (y c) (z d))
			(:instance bit-basic-d (x b) (y c))
			(:instance bit-basic-f (x a) (y (logior c b)) (z d))
			(:instance bit-basic-f (x a) (y c) (z b))
			(:instance bit-basic-f (x (logior a c)) (y b) (z d))
			(:instance logior-nat (i c) (j d))
			(:instance logior-nat (i c) (j b))
			(:instance logior-nat (i a) (j c))))))

(local-defthm logior-bits-4
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(logior (logior (* (expt 2 j) (bits x i j))
				(* (expt 2 j) (bits y i j)))
			(logior (bits x (1- j) 0)
				(bits y (1- j) 0)))))
  :rule-classes ()
  :hints (("Goal"
           ;; The following theory hint was necessary here, though not
           ;; in Russinoff's earlier version.
           :in-theory (disable natp-bits)
           :use (logior-bits-2
                 bits-nat
                 (:instance expt-pos (x j))
                 (:instance integerp-expt (n j))
                 (:instance bits-nat (x y))
                 (:instance bits-nat (i (1- j)) (j 0))
                 (:instance bits-nat (x y) (i (1- j)) (j 0))
                 (:instance logior-bits-3
                            (a (* (expt 2 j) (bits x i j)))
                            (b (bits x (1- j) 0))
                            (c (* (expt 2 j) (bits y i j)))
                            (d (bits y (1- j) 0)))))))

(local-defthm logior-bits-5
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(logior (* (expt 2 j) (logior (bits x i j) (bits y i j)))
			(bits (logior x y) (1- j) 0))))
  :rule-classes ()
  :hints (("Goal"
           ;; The disabling of natp-bits was necessary here, though not
           ;; in Russinoff's earlier version.
           :in-theory (union-theories '(bits-0-rem) (disable natp-bits))
           :use (logior-bits-4
                 bits-nat
                 (:instance bits-nat (x y))
                 (:instance or-dist-c (n j) (x (bits x i j)) (y (bits y i j)))
                 (:instance or-dist-d (n j))))))

(local-defthm logior-bits-6
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(+ (* (expt 2 j) (logior (bits x i j) (bits y i j)))
		   (bits (logior x y) (1- j) 0))))
  :rule-classes ()
  :hints (("Goal"
           ;; The following theory hint was necessary here, though not
           ;; in Russinoff's earlier version.
           :in-theory (disable natp-bits)
           :use (logior-bits-5
                 bits-nat
                 (:instance logior-nat (i x) (j y))
                 (:instance bits-nat (x y))
                 (:instance logior-nat (i (bits x i j)) (j (bits y i j)))
                 (:instance bits-nat (x (logior x y)) (i (1- j)) (j 0))
                 (:instance bits< (x (logior x y)) (i (1- j)) (j 0))
                 (:instance or-dist-b
                            (x (logior (bits x i j) (bits y i j)))
                            (y (bits (logior x y) (1- j) 0))
                            (n j))))))

(local-defthm logior-bits-7
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logior x y) i 0)
		(+ (* (expt 2 j) (bits (logior x y) i j))
		   (bits (logior x y) (1- j) 0))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logior-nat (i x) (j y))
			(:instance bits-bits (x (logior x y)) (m (1+ i)) (n j) (r 0))))))

(defthm bits-logior
    (implies (and (natp x)
		  (natp y)
		  (natp i)
		  (natp j)
		  (>= i j))
	     (equal (bits (logior x y) i j)
		    (logior (bits x i j) (bits y i j))))
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use (logior-bits-6
			logior-bits-7
			(:instance cancel-equal-*
				   (a (expt 2 j))
				   (r (logior (bits x i j) (bits y i j)))
				   (s (bits (logior x y) i j)))
			(:instance logior-nat (i x) (j y))
			(:instance bits-nat (x (logior x y)))
			(:instance bits-nat (x (logior x y)) (i (1- j)) (j 0))
			(:instance or-dist-d (n (1+ i)))
			(:instance expt-pos (x j))))))

(in-theory (disable bits-logior))

(local-defthm logand-bits-1
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logand x y) i 0)
		(logand (+ (* (expt 2 j) (bits x i j))
			   (bits x (1- j) 0))
			(+ (* (expt 2 j) (bits y i j))
			   (bits y (1- j) 0)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use ((:instance rem-logand (n (1+ i)))
			(:instance expo+ (m 1) (n i))
			(:instance bits-bits (m (1+ i)) (n j) (r 0))
			(:instance bits-bits (x y) (m (1+ i)) (n j) (r 0))))))

(local-defthm logand-bits-2
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logand x y) i 0)
		(logand (logior (* (expt 2 j) (bits x i j))
				(bits x (1- j) 0))
			(logior (* (expt 2 j) (bits y i j))
				(bits y (1- j) 0)))))
  :rule-classes ()
  :hints (("Goal"
           ;; The following theory hint was necessary here, though not
           ;; in Russinoff's earlier version.
           :in-theory (disable natp-bits)
           :use (logand-bits-1
			bits-nat
			(:instance bits-nat (x y))
			(:instance bits-nat (i (1- j)) (j 0))
			(:instance bits< (i (1- j)) (j 0))
			(:instance bits-nat (x y) (i (1- j)) (j 0))
			(:instance bits< (x y) (i (1- j)) (j 0))
			(:instance or-dist-b (x (bits x i j)) (n j) (y (bits x (1- j) 0)))
			(:instance or-dist-b (x (bits y i j)) (n j) (y (bits y (1- j) 0)))))))

(local-defthm logand-bits-3
    (implies (and (integerp a) (>= a 0)
		  (integerp b) (>= b 0)
		  (integerp c) (>= c 0)
		  (integerp d) (>= d 0))
	     (= (logand (logior a b) (logior c d))
		(logior (logior (logand a c) (logand c b))
			(logior (logand b d) (logand a d)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bit-basic-h (x (logior a b)) (y c) (z d))
			(:instance bit-basic-h-2 (y a) (z b) (x c))
			(:instance bit-basic-h-2 (y a) (z b) (x d))
			(:instance bit-basic-c (x b) (y c))
			(:instance bit-basic-d (x (logand a d)) (y (logand b d)))
			(:instance logand-nat (i a) (j d))
			(:instance logand-nat (i b) (j d))
			(:instance logior-nat (i a) (j b))))))

(local-defthm logand-bits-4
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logand x y) i 0)
		(logior (logior (logand (* (expt 2 j) (bits x i j))
					(* (expt 2 j) (bits y i j)))
				(logand (* (expt 2 j) (bits y i j))
					(bits x (1- j) 0)))
			(logior (logand (bits x (1- j) 0)
					(bits y (1- j) 0))
				(logand (* (expt 2 j) (bits x i j))
					(bits y (1- j) 0))))))

  :rule-classes ()
  :hints (("Goal"
           ;; The following theory hint was necessary here, though not
           ;; in Russinoff's earlier version.
           :in-theory (disable natp-bits)
           :use (logand-bits-2
                 bits-nat
                 (:instance expt-pos (x j))
                 (:instance integerp-expt (n j))
                 (:instance bits-nat (x y))
                 (:instance bits-nat (i (1- j)) (j 0))
                 (:instance bits-nat (x y) (i (1- j)) (j 0))
                 (:instance logand-bits-3
                            (a (* (expt 2 j) (bits x i j)))
                            (b (bits x (1- j) 0))
                            (c (* (expt 2 j) (bits y i j)))
                            (d (bits y (1- j) 0)))))))

(local-defthm logand-bits-5
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (logand (* (expt 2 j) (bits x i j))
			(* (expt 2 j) (bits y i j)))
		(* (expt 2 j) (logand (bits x i j) (bits y i j)))))
  :rule-classes ()
  :hints (("Goal"
           ;; The following theory hint was necessary here, though not
           ;; in Russinoff's earlier version.
           :in-theory (disable natp-bits)
           :use (bits-nat
                 (:instance expt-pos (x j))
                 (:instance integerp-expt (n j))
                 (:instance bits-nat (x y))
                 (:instance and-dist-b (n j) (x (bits x i j)) (y (* (expt 2 j) (bits y i j))))))))

(local-defthm hack-1
    (implies (and (rationalp x)
		   (rationalp y)
		   (> y 0)
		   (< x y))
	     (< (/ x y) 1))
  :rule-classes ())

(local-defthm logand-bits-6
    (implies (and (integerp y) (>= y 0)
		  (integerp j) (> j 0))
	     (< (/ (bits y (1- j) 0) (expt 2 j))
		1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-pos (x j))
			(:instance integerp-expt (n j))
			(:instance hack-1 (x (bits y (1- j) 0)) (y (expt 2 j)))
			(:instance bits-nat (x y) (i (1- j)) (j 0))
			(:instance bits< (x y) (i (1- j)) (j 0))))))

(local-defthm logand-bits-7
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (logand (* (expt 2 j) (bits x i j))
			(bits y (1- j) 0))
		0))
  :rule-classes ()
  :hints (("Goal"
           ;; The following theory hint was necessary here, though not
           ;; in Russinoff's earlier version.
           :in-theory (disable natp-bits)
           :use (bits-nat
                 logand-bits-6
                 (:instance fl-unique (x (/ (bits y (1- j) 0) (expt 2 j))) (n 0))
                 (:instance expt-pos (x j))
                 (:instance expt-pos (x (- 1 j)))
                 (:instance integerp-expt (n j))
                 (:instance bits-nat (x y) (i (1- j)) (j 0))
                 (:instance bits< (x y) (i (1- j)) (j 0))
                 (:instance bit-basic-a (x (bits x i j)))
                 (:instance and-dist-b (n j) (x (bits x i j)) (y (bits y (1- j) 0)))))))

(local-defthm logand-bits-8
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logand x y) i 0)
		(logior (logior (* (expt 2 j) (logand (bits x i j) (bits y i j)))
				0)
			(logior (logand (bits x (1- j) 0)
					(bits y (1- j) 0))
				0))))
  :rule-classes ()
  :hints (("Goal" :use (logand-bits-4
			logand-bits-5
			logand-bits-7
			(:instance logand-bits-7 (x y) (y x))))))

(local-defthm logand-bits-9
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logand x y) i 0)
		(logior (* (expt 2 j) (logand (bits x i j) (bits y i j)))
			(logand (bits x (1- j) 0)
				(bits y (1- j) 0)))))
  :rule-classes ()
  :hints (("Goal" :use (logand-bits-8
			bits-nat
			(:instance bits-nat (x y))
			(:instance expt-pos (x j))
			(:instance integerp-expt (n j))
			(:instance bits-nat (i (1- j)) (j 0))
			(:instance bits-nat (x y) (i (1- j)) (j 0))
			(:instance logand-nat (i (bits x (1- j) 0)) (j (bits y (1- j) 0)))
			(:instance logand-nat (i (bits x i j)) (j (bits y i j)))
			(:instance bit-basic-b (x (* (expt 2 j) (logand (bits x i j) (bits y i j)))))
			(:instance bit-basic-b (x (logand (bits x (1- j) 0) (bits y (1- j) 0))))))))

(local-defthm logand-bits-10
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logand x y) i 0)
		(logior (* (expt 2 j) (logand (bits x i j) (bits y i j)))
			(bits (logand x y) (1- j) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use (logand-bits-9
			(:instance rem-logand (n j))))))

(local-defthm logand-bits-11
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logand x y) i 0)
		(+ (* (expt 2 j) (logand (bits x i j) (bits y i j)))
		   (bits (logand x y) (1- j) 0))))
  :rule-classes ()
  :hints (("Goal"
           ;; The following theory hint was necessary here, though not
           ;; in Russinoff's earlier version.
           :in-theory (disable natp-bits)
           :use (logand-bits-10
                 bits-nat
                 (:instance logand-nat (i x) (j y))
                 (:instance bits-nat (x y))
                 (:instance logand-nat (i (bits x i j)) (j (bits y i j)))
                 (:instance bits-nat (x (logand x y)) (i (1- j)) (j 0))
                 (:instance bits< (x (logand x y)) (i (1- j)) (j 0))
                 (:instance or-dist-b
                            (x (logand (bits x i j) (bits y i j)))
                            (y (bits (logand x y) (1- j) 0))
                            (n j))))))

(local-defthm logand-bits-12
    (implies (and (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp i) (>= i j)
		  (integerp j) (> j 0))
	     (= (bits (logand x y) i 0)
		(+ (* (expt 2 j) (bits (logand x y) i j))
		   (bits (logand x y) (1- j) 0))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance logand-nat (i x) (j y))
			(:instance bits-bits (x (logand x y)) (m (1+ i)) (n j) (r 0))))))

(defthm bits-logand
    (implies (and (natp x)
		  (natp y)
		  (natp i)
		  (natp j)
		  (>= i j))
	     (equal (bits (logand x y) i j)
		    (logand (bits x i j) (bits y i j))))
  :hints (("Goal" :in-theory (enable bits-0-rem)
		  :use (logand-bits-11
			logand-bits-12
			(:instance cancel-equal-*
				   (a (expt 2 j))
				   (r (logand (bits x i j) (bits y i j)))
				   (s (bits (logand x y) i j)))
			(:instance logand-nat (i x) (j y))
			(:instance bits-nat (x (logand x y)))
			(:instance bits-nat (x (logand x y)) (i (1- j)) (j 0))
			(:instance rem-logand (n (1+ i)))
			(:instance expt-pos (x j))))))

(in-theory (disable bits-logand))

(in-theory (enable comp1))

(defthm natp-comp1
    (implies (and (natp n)
		  (bvecp x n))
	     (natp (comp1 x n)))
    :rule-classes
    ;; It seems a good idea to make this a :rewrite rule, not just a
    ;; :type-prescription rule, because of the bvecp hypothesis.
    (:type-prescription :rewrite)
    :hints (("Goal" :in-theory (enable bvecp natp comp1))))

(in-theory (disable comp1))

;; !! Should the following few lemmas be local?  [YES]

(defthm bits-comp1-1
    (implies (and (integerp m) (> m i)
		  (integerp i) (>= i j) (>= i 0)
		  (integerp j) (>= j 0)
		  (integerp x) (>= x 0) (< x (expt 2 m)))
	     (= (bits (comp1 x m) i j)
		(fl (/ (comp1 (rem x (expt 2 (1+ i))) (1+ i))
		       (expt 2 j)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
		  :use ((:instance comp1-rem (n (1+ i)))))))

(in-theory (enable comp1))

(defthm bits-comp1-2
    (implies (and (integerp m) (> m i)
		  (integerp i) (>= i j) (>= i 0)
		  (integerp j) (>= j 0)
		  (integerp x) (>= x 0) (< x (expt 2 m)))
	     (= (bits (comp1 x m) i j)
		(fl (+ (expt 2 (1+ (- i j)))
		       (/ (- (1+ (rem x (expt 2 (1+ i)))))
			  (expt 2 j))))))
  :rule-classes ()
  :hints (("Goal" :use (bits-comp1-1
			(:instance expt- (a (1+ i)) (b j))))))

(defthm bits-comp1-3
    (implies (and (integerp m) (> m i)
		  (integerp i) (>= i j) (>= i 0)
		  (integerp j) (>= j 0)
		  (integerp x) (>= x 0) (< x (expt 2 m)))
	     (= (bits (comp1 x m) i j)
		(+ (expt 2 (1+ (- i j)))
		   (fl (/ (- (1+ (rem x (expt 2 (1+ i)))))
			  (expt 2 j))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable a10)
		  :use (bits-comp1-2
			(:instance integerp-expt (n (- (1+ i) j)))
			(:instance fl+int
				   (x (/ (- (1+ (rem x (expt 2 (1+ i))))) (expt 2 j)))
				   (n (expt 2 (1+ (- i j)))))))))

(defthm bits-comp1-4
    (implies (and (integerp m) (> m i)
		  (integerp i) (>= i j) (>= i 0)
		  (integerp j) (>= j 0)
		  (integerp x) (>= x 0) (< x (expt 2 m)))
	     (= (bits (comp1 x m) i j)
		(comp1 (fl (/ (rem x (expt 2 (1+ i)))
			      (expt 2 j)))
		       (1+ (- i j)))))
  :rule-classes ()
  :hints (("Goal" :use (bits-comp1-3
			(:instance rem>=0 (m x) (n (expt 2 (1+ i))))
			(:instance floor-m+1 (m (rem x (expt 2 (1+ i)))) (n (expt 2 j)))))))

(defthm bits-comp1-5
    (implies (and (integerp m) (> m i)
		  (integerp i) (>= i j) (>= i 0)
		  (integerp j) (>= j 0)
		  (integerp x) (>= x 0) (< x (expt 2 m)))
	     (= (bits (comp1 x m) i j)
		(comp1 (bits x i j) (1+ (- i j)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bits)
		  :use (bits-comp1-4))))

(defthm bits-comp1
    (implies (and (natp m)
		  (natp i)
		  (natp j)
		  (> m i)
		  (>= i j)
		  (bvecp x m))
	     (equal (bits (comp1 x m) i j)
		    (comp1 (bits x i j) (1+ (- i j)))))
  :hints (("Goal" :use (bits-comp1-5))))

(in-theory (disable bits-comp1))

(in-theory (enable comp1))

(local-defthm logxor-bits-1
    (implies (and (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n))
		  (integerp n) (>= n i)
		  (integerp i) (>= i j)
		  (integerp j) (>= j 0)
                  (> n 0)) ; last hyp not needed in Russinoff's version
	     (= (bits (logxor x y) i j)
		(logior (logand (bits x i j) (bits (comp1 y n) i j))
			(logand (bits y i j) (bits (comp1 x n) i j)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-comp1 bvecp-comp1 comp1
                                      ;; Disabling natp-bits was not
                                      ;; necessary in Russinoff's version.
                                      natp-bits)
		  :use (logxor-rewrite
			bvecp-comp1
			(:instance bvecp-comp1 (x y))
			(:instance bits-logior (x (logand x (comp1 y n))) (y (logand y (comp1 x n))))
			(:instance logand-nat (i x) (j (comp1 y n)))
			(:instance logand-nat (i y) (j (comp1 x n)))
			(:instance bits-logand (y (comp1 y n)))
			(:instance bits-logand (x y) (y (comp1 x n)))))))

(local-defthm logxor-bits-2
    (implies (and (integerp x) (>= x 0) (< x (expt 2 n))
		  (integerp y) (>= y 0) (< y (expt 2 n))
		  (integerp n) (> n i)
		  (integerp i) (>= i j)
		  (integerp j) (>= j 0))
	     (= (bits (logxor x y) i j)
		(logior (logand (bits x i j) (comp1 (bits y i j) (1+ (- i j))))
			(logand (bits y i j) (comp1 (bits x i j) (1+ (- i j)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable integerp-comp1 bvecp-comp1 comp1)
		  :use (logxor-bits-1
			(:instance bits-comp1 (m n))
			(:instance bits-comp1 (x y) (m n))))))

(defthm bits-logxor
    (implies (and (bvecp x n) ; Free variable n is bound here
		  (bvecp y n)
		  (natp n)
		  (natp i)
		  (natp j)
		  (> n i)
		  (>= i j))
	     (equal (bits (logxor x y) i j)
		    (logxor (bits x i j) (bits y i j))))
  :hints (("Goal" :in-theory (disable integerp-comp1 bvecp-comp1 comp1)
		  :use (logxor-bits-2
			(:instance logxor-rewrite (x (bits x i j)) (y (bits y i j)) (n (1+ (- i j))))
			(:instance bits<)
			(:instance bits-nat)
			(:instance bits< (x y))
			(:instance bits-nat (x y))))))

(in-theory (disable bits-logxor))

(defthm bits-logxor-upper-slice
    (implies (and (equal n (+ 1 i))
                  (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp i)
		  (natp j)
		  (> n i)
		  (>= i j))
	     (equal (bits (logxor x y) i j)
		    (logxor (bits x i j) (bits y i j))))
    :hints (("Goal" :use ((:instance bits-logxor (n (+ 1 i)))))))

(in-theory (disable bits-logxor-upper-slice))

(defthm cat-nat
    (implies (and (natp x)
		  (natp y)
		  (natp n))
	     (natp (cat x y n)))
    :rule-classes (:type-prescription :rewrite))

(local-defthm hack-10
    (implies (and (integerp x)
		  (integerp y)
		  (< x y))
	     (<= x (1- y)))
  :rule-classes ())

(local-defthm bvecp-cat-1
    (implies (and (natp n)
		  (natp p)
		  (bvecp x m)
		  (natp m)
		  (bvecp y n)
		  (>= p (+ m n)))
	     (bvecp (cat x y n) p))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable natp bvecp cat)
		  :use (expo+
			(:instance hack-10 (y (expt 2 m)))
			(:instance expt-monotone (m p))
			(:instance integerp-expt (n m))
			(:instance expt-monotone (m p) (n (+ m n)))))))

(defthm bvecp-cat
    (implies (and (natp n)
		  (natp p)
		  (>= p n)
		  (bvecp x (- p n))
		  (bvecp y n))
	     (bvecp (cat x y n) p))
  :hints (("Goal" :in-theory (enable natp bvecp)
		  :use ((:instance bvecp-cat-1 (m (- p n)))))))

(in-theory (disable bvecp-cat))

(defthm bits-cat-1
    (implies (and (natp x)
		  (natp y)
		  (natp j)
		  (natp i)
		  (natp n)
		  (>= n (1+ i)))
	     (equal (bits (cat x y n) i j)
		    (bits y i j)))
  :hints (("Goal"
           ;; The following hint wasn't necessary in Russinoff's version.
           :in-theory (disable integerp-expt)
           :use ((:instance rem-bits (x (cat x y n)))
			(:instance integerp-expt (n (- n (1+ i))))
			(:instance expt-pos (x (- n (1+ i))))
			(:instance rem+ (n (expt 2 (1+ i))) (m y) (a (* x (expt 2 (- n (1+ i))))))))))

(defthm natp-posp-expt
  (implies (natp n)
           (posp (expt 2 n)) ; modified for v2-8 by Daron V. and Pete M.
           )
  :rule-classes (:type-prescription :rewrite))

; While we are at it, we prove the following, which is needed in the
; fpaf3a proof (far.lisp, lemma hack-1).
(defthm expt-positive
  (implies (and (rationalp x)
		(posp base)  ; modified for v2-8 by Daron V. and Pete M.
                )
           (and (rationalp (expt base x))
                (< 0 (expt base x))))
  :rule-classes (:type-prescription :rewrite))

(defthm bits-cat-2
    (implies (and (natp n)
		  (natp j)
		  (>= j n)
		  (natp i)
		  (>= i j)
		  (natp x)
		  (bvecp y n))
	     (equal (bits (cat x y n) i j)
		    (bits x (- i n) (- j n))))
  :hints (("Goal" :use ((:instance fl-unique (x (/ (cat x y n) (expt 2 n))) (n x))
			(:instance expt-pos (x (- n)))
			(:instance bit-bits-a (x (cat x y n)) (k n))))))

(defthm bitn-cat-1
    (implies (and (natp x)
		  (natp y)
		  (natp i)
		  (natp n)
		  (>= n (1+ i)))
	     (equal (bitn (cat x y n) i)
		    (bitn y i)))
  :hints (("Goal" :use ((:instance bit+*k (x y) (k x) (m n) (n i))))))

(defthm bitn-cat-2
    (implies (and (natp n)
		  (natp i)
		  (>= i n)
		  (natp x)
		  (bvecp y n))
	     (equal (bitn (cat x y n) i)
		    (bitn x (- i n))))
  :hints (("Goal" :use ((:instance bit+*k-2 (x y) (k x) (m n) (n i))))))

(defthm cat-0-rewrite
    (implies (natp x)
	     (equal (cat 0 x n) x))
    :hints (("Goal" :in-theory (enable natp cat))))

(defun shft (x s l)
  (rem (fl (* (expt 2 s) x)) (expt 2 l)))

(defthm bvecp-shft
    (implies (and (natp x)
		  (natp n)
		  (integerp s))
	     (bvecp (shft x s n) n))
  :hints (("Goal" :in-theory (enable bvecp natp)
		  :use ((:instance n<=fl (x (* (expt 2 s) x)) (n 0))
			(:instance rem>=0 (m (fl (* (expt 2 s) x))) (n (expt 2 n)))
			(:instance rem<n (m (fl (* (expt 2 s) x))) (n (expt 2 n)))
			(:instance integerp-expt (n s))
			(:instance integerp-expt)
			(:instance expt-pos (x n))
			(:instance expt-pos (x s))))))

(defthm natp-shft
    (implies (and (natp x)
		  (natp n)
		  (integerp s))
	     (natp (shft x s n)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :in-theory (enable bvecp natp)
		  :use (bvecp-shft))))

(in-theory (disable bvecp))

; The following rule allows us to relieve (integerp x) hypotheses when
; a rule applies to show (natp x).
(defthm natp-integerp
  (implies (natp x)
           (integerp x)))

; Avoid looping:
(theory-invariant
 (not (and (active-runep '(:rewrite natp-integerp-bridge))
           (active-runep '(:definition natp))))
 :key :natp-integerp-bridge-invariant)

