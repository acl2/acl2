(in-package "ACL2")

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

;(defund ocat (x y n)
;  (declare (xargs :guard t))
;  (+ (* (expt 2 (nfix n)) (nfix x)) (nfix y)))

(defund all-ones (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (if (zp n)
      0 ;degenerate case
    (1- (expt 2 n))))

(include-book "cat-def")
(local (include-book "../arithmetic/top")) ;try
(local (include-book "bits"))
(local (include-book "bvecp"))

(local (in-theory (enable expt-minus)))

#|
Concatenate the M-bit value X onto the N-bit value Y.  X will occupy the high bits of the result.

(cat x m y n) is well-defined only when the following predicate is true:

(and (natp m)
     (bvecp x m)
     (natp n)
     (bvecp y n))

|#

(defthm cat-nonnegative-integer-type
  (and (integerp (cat x m y n))
       (<= 0 (cat x m y n)))
  :hints (("Goal" :in-theory (enable cat)))
  :rule-classes (:type-prescription)
  )

;this rule is no better than cat-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-cat)))

;just a rewrite rule
(defthm cat-natp
  (natp (cat x m y n)))

;disable?
(defthm cat-0
  (implies (and (case-split (bvecp y n))
                (case-split (integerp n))
                (case-split (integerp m))
                (case-split (<= 0 m))
                )
           (equal (cat 0 m y n) y))
  :hints (("Goal" :in-theory (enable cat bits-tail))))

;BOZO just use this one??
(defthm cat-0-alt
  (implies (and ;(case-split (bvecp y n))
                (case-split (integerp n))
                (case-split (integerp m))
                (case-split (<= 0 m))
                )
           (equal (cat 0 m y n) (bits y (1- n) 0)))
  :hints (("Goal" :in-theory (enable cat bits-tail))))

;We can rely on bits-tail to complete the simplification down to x if desired.
(defthm cat-with-n-0
  (equal (binary-cat x m y 0)
         (bits x (1- m) 0))
  :hints (("goal" :in-theory (enable cat))))

(local (in-theory (enable bits-tail)))

(defthm cat-with-n-0-alt
 (implies (case-split (bvecp x m))
           (equal (cat x m y 0)
                  x)))

;We can rely on bits-tail to complete the simplification down to y if desired.
(defthm cat-with-m-0
  (equal (binary-cat x 0 y n)
         (bits y (1- n) 0))
  :hints (("goal" :in-theory (enable cat))))

(defthm cat-with-m-0-alt
  (implies (case-split (bvecp y n))
           (equal (cat x 0 y n)
                  y)))

;change this behavior??
(defthm cat-with-n-not-a-natural
  (implies (or (not (integerp n))
               (< n 0))
           (equal (cat x m y n)
                  0))
  :hints (("Goal" :in-theory (enable cat))))

(defthm cat-with-m-not-a-natural
  (implies (or (not (integerp m))
               (< m 0))
           (equal (cat x m y n)
                  0))
  :hints (("Goal" :in-theory (enable cat))))

#|
;used to transfer theorems about ocat to theorems about cat
(defthmd cat-ocat
    (equal (binary-cat x m y n)
	   (if (or (not (integerp m))
		   (< m 0)
		   (not (integerp n))
		   (< n 0)
		   )
	       0
	     (ocat (bits x (1- m) 0)
		   (bits y (1- n) 0)
		   n)))
  :hints (("Goal" :in-theory (enable ocat cat))))
|#

(local (defthm hack-10
    (implies (and (integerp x)
		  (integerp y)
		  (< x y)
                  )
	     (<= x (1- y)))
  :rule-classes ()))

(defthm cat-bvecp-simple
  (bvecp (cat x m y n) (+ m n))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bvecp cat expt-split)
                              '(expt-compare EXPT-COMPARE-EQUAL ))
		  :use ((:instance expt-split (i m) (j n) (r 2))
			(:instance hack-10 (x (BITS X (1- M) 0)) (y (expt 2 m)))
			(:instance expt-weak-monotone (m p))
			(:instance expt-weak-monotone (m k) (n (+ m n)))))))


(defthm cat-bvecp
  (implies (and (<= (+ m n) k)
                (case-split (integerp k)))
           (bvecp (cat x m y n) k))
  :hints (("Goal" :in-theory (disable cat-bvecp-simple)
           :use cat-bvecp-simple)))

#|

these aren't right any more?

(defthm cat-with-x-not-a-natural
  (implies (or (not (integerp x))
               (< x 0))
           (equal (cat x m y n)
                  0))
  :hints (("Goal" :in-theory (enable cat))))

(defthm cat-with-y-not-a-natural
  (implies (or (not (integerp y))
               (< y 0))
           (equal (cat x y n)
                  (* (nfix x) (expt 2 (nfix n)))))
  :hints (("Goal" :in-theory (enable cat-ocat))))

|#

;move
(defthm hack11
 (implies (and (< x z)
               (integerp x)
               (integerp z)
               (<= 0 y)
               (< y 1))
          (< (+ x y) z)))

;move!
(defthm expt-bound-hack
 (implies (and (< y (expt 2 i))
               (< x (expt 2 (- k i)))
               (<= 0 x)
               (<= 0 y)
               (<= i k)
               (integerp k)
               (integerp i)
               (integerp x)
               (integerp y)
               )
          (< (+ y (* (expt 2 i) x)) (expt 2 k)))
 :hints (("Goal" :in-theory (e/d ( expt-split expt-minus)
                                 (LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE
                                  LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-RIGHT-HAND-SIDE))
          :use (:instance  mult-both-sides-of-<-by-positive (a (+ y (* x (expt 2 i)))) (b (expt 2 k))
                           (c (/ (expt 2 i))))))
 )



(defthm cat-associative
  (implies (and (case-split (<= (+ m n) p)) ;gen?
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (<= 0 q))
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp p))
                (case-split (integerp q))
                )
           (equal (cat (cat x m y n) p z q)
                  (cat x m (cat y n z q) (+ n q))))
  :hints (("Goal" :in-theory (enable cat))))

;prove from something more general (cat-equal-split??)
;BOZO move hyps to conclusion?
(defthm cat-equal-0
  (implies (and (case-split (bvecp x m))
                (case-split (bvecp y n))
                (case-split (natp n))
                (case-split (natp m))
                )
           (equal (equal (cat x m y n) 0)
                  (and (equal x 0)
                       (equal y 0))))
  :hints (("Goal" :in-theory (enable cat bits-tail bvecp)))
  )

(defthm cat-combine-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep m)
                              (quotep y)
                              (quotep n)))
                (equal (+ n p) r)
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (<= 0 p))
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp p))
                )
           (equal (cat x m (cat y n z p) r)
                  (cat (cat x m y n) (+ m n) z p))))

;allows r to be > n+p
(defthm cat-combine-constants-gen
  (implies (and (syntaxp (and (quotep x)
                              (quotep m)
                              (quotep y)
                              (quotep r)
                              (quotep p)))
                (case-split (<= (+ n p) r))
                (case-split (bvecp y n))
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (<= 0 p))
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp p))
                (case-split (integerp r))
                )
           (equal (cat x m (cat y n z p) r)
                  (cat (cat x m y (+ r (- p))) (+ m r (- p)) z p)))
  :hints (("goal" :in-theory (enable bits-tail)
           :expand ((binary-cat y n z p)
                           (binary-cat y (+ r (* -1 p)) z p)))))

(defthm cat-constant-equal-constant-hack
  (implies (and (syntaxp (and (quotep k1) (quotep k2)))
                (case-split (bvecp x n))
                (case-split (bvecp k1 m))
                (case-split (rationalp k2))
                (case-split (natp n))
                (case-split (natp m))
                )
           (equal (equal (cat k1 m x n) k2)
                  (equal x (- k2 (* (expt 2 n) k1)))))
  :hints (("Goal" :in-theory (enable cat bvecp))))

(defthm cat-upper-bound
  (< (cat x m y n)
     (expt 2 (+ m n)))
  :rule-classes (:rewrite :linear)
  :hints (("goal"
           :in-theory (set-difference-theories
                       (enable cat)
                       '()))))

;perhaps the :linear rule cat-upper-bound is enough, but this may help stupid hyps be rewritten away
(defthm cat-compare-to-constant-1
  (implies (and (syntaxp (quotep k))
                (<= (expt 2 (+ m n)) k))
           (< (cat x m y n) k))
  :hints (("goal" :in-theory (disable cat-upper-bound)
           :use cat-upper-bound)))

;provides a tighter bound
(defthm cat-upper-bound-tight
  (implies (and (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (<= (cat x m y n)
               (1- (expt 2 (+ n m)))))
  :hints (("goal" :use cat-upper-bound
           :in-theory (set-difference-theories
                       (enable)
                       '(cat-upper-bound)))))


(defthm cat-compare-to-constant-2
  (implies (and (syntaxp (quotep k))
                (<= (1- (expt 2 (+ m n))) k)
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (not (< k (cat x m y n))))
  :hints (("goal" :in-theory (disable cat-upper-bound)
           :use cat-upper-bound)))

;BOZO consider adding?
;problem if we case-split something that turns out to be false?
(defthm bits-with-i-not-an-integer-2
  (implies (case-split (not (integerp i)))
           (equal (bits x i j)
                  0)))

(defthm bits-with-j-not-an-integer-2
  (implies (case-split (not (integerp j)))
           (equal (bits x i j)
                  0)))

;also case-split that i>=j in any call to bits?


;loops with bits-<-1
;BOZO add theory invariant!
;BOZO ask matt about parity..
(defthmd bits-equal-0-to-bound
  (equal (equal 0 (bits x i j))
         (< (bits x i j) 1)))

;we had a special case where j was 0, but I think this is better (it's certainly more general):
;better name?
;think about whether this can be proved without opening bits (including bits-plus-bits??)
;prove bvecp-bits from this??
;the regular bits-bvecp should fire first...
(defthm bits-slice-zero-gen
  (implies (and (case-split (<= 0 k))
                (case-split (integerp k))
                (case-split (integerp j))
                )
           (equal (bvecp (bits x i j) k)
                  (equal 0 (bits x i (+ k j)))))
  :otf-flg t
  :hints (("Goal" :use (:instance bits-plus-bits (n i) (m j) (p (+ k j)))
           :in-theory (e/d (bits-equal-0-to-bound bvecp expt-strong-monotone-linear) (bits-<-1)))))

(encapsulate
 ()

 (local (defthm cat-bvecp-rewrite-case-1-a
          (implies (and (<= n k) ;this case
                        (< k (+ m n))
                        (<= 0 n)
                        (integerp k)
                        (integerp n)
                        )
                   (implies (bvecp (cat x m y n) k)
                            (bvecp (bits x (1- m) 0) (+ k (* -1 n))) ;the BITS call around x is weird but necessary
                            ))
          :rule-classes nil
          :otf-flg t
          :hints (("Goal" :in-theory (e/d (cat bvecp expt-split) ( expt-inverse  bits-slice-zero-gen))))))

 (local (defthm cat-bvecp-rewrite-case-1-a-better
          (implies (and (<= n k) ;this case
                        (< k (+ m n))
                        (<= 0 n)
                        (integerp k)
                        (integerp n)
                        )
                   (implies (bvecp (cat x m y n) k)
                            (equal 0 (bits x (1- m) (+ k (* -1 n))))
                            ))
          :rule-classes nil
          :otf-flg t
          :hints (("Goal" :use  cat-bvecp-rewrite-case-1-a ))))

;move!
;this can help, especially when we aren't multiplying through by inverted factors
 (defthm bits-upper-bound-new
   (< (* (/ (expt 2 i)) (bits x (1- i) 0)) 1)
   :hints (("Goal" :in-theory (disable expt-inverse)))
   :rule-classes (:rewrite :linear)
   )

;make a lemma about bvecp of (+ (BITS Y (+ -1 N) 0) (* (EXPT 2 N) (BITS X (+ -1 M) 0))) ?
 (local (defthm cat-bvecp-rewrite-case-1-b
          (implies (and (<= n k) ;this case
                        (< k (+ m n))
                        (integerp k)
                        )
                   (implies (bvecp (bits x (1- m) 0) (- k n))
                            (bvecp (cat x m y n) k))) ;the BITS call around x is weird but necessary?
          :rule-classes nil
          :hints (("Goal" :in-theory (e/d (cat bvecp expt-split
                                               EXPT-minus
                                               )
                                          ( expt-inverse
;these must be disabled, or  bits-upper-bound-new fails to do its job
                                               LESS-THAN-MULTIPLY-THROUGH-BY-inverted-factor-FROM-LEFT-HAND-SIDE
                                               LESS-THAN-MULTIPLY-THROUGH-BY-inverted-factor-FROM-RIGHT-HAND-SIDE
                                               ))))))



 (local (defthm cat-bvecp-rewrite-case-1-b-better
          (implies (and (<= n k) ;this case
                        (< k (+ m n))
                        (integerp k)
                        )
                   (implies (equal 0 (bits x (1- m) (+ k (* -1 n))))
                            (bvecp (cat x m y n) k))) ;the BITS call around x is weird but necessary?
          :rule-classes nil
          :hints (("Goal":use  cat-bvecp-rewrite-case-1-b))))


 (local (defthm cat-bvecp-rewrite-case-1
          (implies (and (<= n k) ;this case
                        (< k (+ m n))
                        (case-split (<= 0 n))
                        (case-split (integerp k))
                        (case-split (integerp n))
                        )
                   (equal (bvecp (cat x m y n) k)
                          (equal 0 (bits x (1- m) (+ k (* -1 n)))))) ;the BITS call around x is weird but necessary?
          :hints (("Goal" :use ( cat-bvecp-rewrite-case-1-b-better  cat-bvecp-rewrite-case-1-a-better)))
          ))






 (local (defthm cat-bvecp-rewrite-case-2-a
          (implies (and (< k n) ;this case
                        (<= 0 k)
                        (natp m) (natp n) (natp k)
                        (integerp n)
                        (integerp k)
                        )
                   (implies (bvecp (cat x m y n) k)
                            (and (equal (bits x (1- m) 0) 0)
                                 (bvecp (bits y (1- n) 0) k))))
          :rule-classes nil
          :otf-flg t
          :hints (("Goal"
                   :use (
                         )
                   :in-theory (e/d (cat bvecp bits-equal-0-to-bound expt-strong-monotone-linear) (bits-<-1
                                                                                                  BITS-SLICE-ZERO-GEN
                                                                                                  ))))))


 (local (defthm cat-bvecp-rewrite-case-2-a-better
          (implies (and (< k n) ;this case
                        (<= 0 k)
                        (<= 0 m)
                        (integerp m)
                        (integerp n)
                        (integerp k)
                        )
                   (implies (bvecp (cat x m y n) k)
                            (and (equal 0 (bits x (1- m) 0))
                                 (equal 0 (bits y (1- n) k)))))
          :rule-classes nil
          :otf-flg t
          :hints (("Goal"
                   :use (cat-bvecp-rewrite-case-2-a)))))

 (local (defthm cat-bvecp-rewrite-case-2-b
          (implies (and (< k n) ;this case
                        (<= 0 k)
                        (integerp n)
                        (integerp k)
                        )
                   (implies (and (equal (bits x (1- m) 0) 0)
                                 (bvecp (bits y (1- n) 0) k))
                            (bvecp (cat x m y n) k)))
          :rule-classes nil
          :otf-flg t
          :hints (("Goal"
                   :use (
                         )
                   :in-theory (e/d (cat
                                    bits-equal-0-to-bound
                                    expt-strong-monotone-linear
                                    bvecp expt-split)
                                   (;CANCEL-IN-PRODS-<-1-OF-2-WITH-1-OF-1
                                    ;CANCEL-TIMES-<-ERIC-1-BETTER-ALT
                                    bits-<-1

                                    expt-inverse
                                    BITS-SLICE-ZERO-GEN))))))

 (local (defthm cat-bvecp-rewrite-case-2-b-better
          (implies (and (< k n) ;this case
                        (<= 0 k)
                        (integerp n)
                        (integerp k)
                        )
                   (implies (and (equal (bits x (1- m) 0) 0)
                                 (equal 0 (bits y (1- n) k)))
                            (bvecp (cat x m y n) k)))
          :rule-classes nil
          :otf-flg t
          :hints (("Goal"
                   :use (cat-bvecp-rewrite-case-2-b)))))

 (local (defthm cat-bvecp-rewrite-case-2
          (implies (and (< k n) ;this case
                        (<= 0 k)
                        (<= 0 m)
                        (integerp m)
                        (integerp n)
                        (integerp k)
                        )
                   (equal (bvecp (cat x m y n) k)
                          (and (equal 0 (bits x (1- m) 0))
                               (equal 0 (bits y (1- n) k)))))
          :otf-flg t
          :hints (("Goal"
                   :use (cat-bvecp-rewrite-case-2-a-better
                         cat-bvecp-rewrite-case-2-b-better
                         )
                   :in-theory (e/d () ())))))

 (defthmd cat-bvecp-rewrite
   (implies (and (case-split (<= 0 k))
                 (case-split (<= 0 n))
                 (case-split (<= 0 m))
                 (case-split (integerp n))
                 (case-split (integerp m))
                 (case-split (integerp k))
                 )
            (equal (bvecp (cat x m y n) k)
                   (if (<= (+ m n) k)
                       t
                     (if (<= n k)
                         (equal 0 (bits x (1- m) (+ k (* -1 n))))
                       (and (equal 0 (bits x (1- m) 0))
                            (equal 0 (bits y (1- n) k))))))))

 ) ;end the encapsulate

(defthm cat-bvecp-rewrite-constants
  (implies (and (syntaxp (and (quotep k) (quotep m) (quotep n)))
                (case-split (<= 0 k))
                (case-split (<= 0 n))
                (case-split (<= 0 m))
                (case-split (integerp n))
                (case-split (integerp m))
                (case-split (integerp k))
                )
           (equal (bvecp (cat x m y n) k)
                  (if (<= (+ m n) k)
                      t
                    (if (<= n k)
                        (equal 0 (bits x (1- m) (+ k (* -1 n))))
                      (and (equal 0 (bits x (1- m) 0))
                           (equal 0 (bits y (1- n) k)))))))
  :hints (("Goal" :by cat-bvecp-rewrite)))


#|
Art's example:

(thm (implies (and (natp i) (natp m) (natp n) (bvecp x i))
              (bvecp (cat x m y n) (+ i n)))
     )
|#

;k is a free variable.
;There is no real analogue of this for y (that is, we can't change n to something smaller).
(defthm cat-tighten-x
  (implies (and (bvecp x k) ;k becomes bound here
                (< k m) ;if k=m, this rule can loop
                (case-split (<= 0 k))
                (case-split (integerp k))
                (case-split (integerp m))
                )
           (equal (cat x m y n)
                  (cat x k y n)))
  :hints (("Goal" :in-theory (enable cat))))














(defthm cat-equal-y
  (implies (and (bvecp y (+ m n))
                (case-split (integerp m))
                (case-split (<= 0 m))
                (case-split (integerp n))
                (case-split (<= 0 n)))
           (equal (equal y (binary-cat x m y n))
                  (equal (bits y (+ -1 m n) n)
                         (bits x (1- m) 0))))
  :hints (("Goal" :in-theory (enable cat a15)
           :use (:instance bits-plus-bits (x y) (n  (+ -1 m n)) (m 0) (p n))))
  )

(defthm cat-equal-y-alt
  (implies (and (case-split (integerp m))
                (case-split (<= 0 m))
                (case-split (integerp n))
                (case-split (<= 0 n)))
           (equal (equal y (binary-cat x m y n))
                  (if (bvecp y (+ m n))
                      (equal (bits y (+ -1 m n) n)
                             (bits x (1- m) 0))
                    nil)))
  :hints (("Goal" :in-theory (disable  cat-equal-y)
           :use  cat-equal-y))
)

(defthm cat-equal-bits-of-y
  (implies (and; (case-split (bvecp y n))
;                (case-split (bvecp x m))
                (case-split (integerp m))
                (case-split (<= 0 m))
                (case-split (integerp n))
                (case-split (<= 0 n)))
           (equal (equal (bits y (1- n) 0) (binary-cat x m y n))
                  (equal (bits x (1- m) 0) 0)))
  :hints (("goal" :in-theory (enable binary-cat)))
   )

;requires y to be a bvecp of length n
;drop this one?
(defthm cat-equal-y-special
  (implies (and (case-split (bvecp y n))
                (case-split (integerp m))
                (case-split (<= 0 m)) ;gen!
                (case-split (integerp n))
                (case-split (<= 0 n)))
           (equal (equal y (binary-cat x m y n))
                  (equal 0 (bits x (1- m) 0))))
  :hints (("Goal" :use cat-equal-bits-of-y)) ;drop this hint
  )

;enable?
;make into 2 separate lemmas (can drop the bits from x or from y)
(defthmd cat-ignores-bits
  (equal (cat (bits x (1- m) 0)
              m (bits y (1- n) 0)
              n)
         (cat x m y n))
  :hints (("goal" :in-theory (enable cat))))

(defthmd bits-cat-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp m))
                (case-split (<= 0 m))
                )
           (equal (bits (cat x m y n) i j)
                  (bits y i j)))
  :hints (("Goal" :in-theory (enable cat))))

;move!


(defthmd bits-cat-2-1
  (implies (and (<= n j) ;case 2
                (< i (+ m n))  ;case 2-1
                (case-split (natp n))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (natp m))
                )
           (equal (bits (cat x m y n) i j)
                  (bits x (- i n) (- j n))))
  :hints (("Goal" :in-theory (enable cat))))

(defthmd bits-cat-2-2
  (implies (and (<= n j)  ;case 2
                (<= (+ m n) i)  ;case 2-1
                (case-split (natp n))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (natp m))
                )
           (equal (bits (cat x m y n) i j)
                  (bits x (+ m -1) (- j n))))
  :hints (("Goal" :in-theory (enable cat)))
  )

;note the IF in the conclusion
(defthmd bits-cat-2
  (implies (and (<= n j)  ;case 2
                (case-split (natp n))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (natp m))
                )
           (equal (bits (cat x m y n) i j)
                  (bits x (if (< i (+ m n))
                              (- i n)
                            (1- m))
                        (- j n))))
  :hints (("Goal" :in-theory (enable cat)))
  )


;Note the IF in the conclusion
(defthmd bits-cat-3
  (implies (and (>= i n)
                (< j n)
                (case-split (natp n))
                (case-split (natp m))
                (case-split (natp i))
                (case-split (natp j))
                )
           (equal (bits (cat x m y n) i j)
                  (cat (bits x (if (< i (+ m n))
                                    (- i n)
                                  (1- m))
                              0)
                        (+ 1 (- i n))
                        (bits y (1- n) j)
                        (- n j))))
  :hints (("Goal" :use (:instance bits-plus-bits (x (cat x m y n)) (p n) (n i) (m j))
           :in-theory (enable cat   bits-plus-mult-1))))

;includes both bits-cat-1, bits-cat-2, and bits-cat-3
;we expect the indices to be constants, so this won't cause case-splits
;gen
(defthm bits-cat
  (implies (and (case-split (natp n))
                (case-split (natp m))
                (case-split (natp i))
                (case-split (natp j)))
           (equal (bits (cat x m y n) i j)
                  (if (< i n)
                      (bits y i j)
                    (if (>= j n)
                        (bits x (if (< i (+ m n))
                                    (- i n)
                                  (1- m))
                              (- j n))
                      (cat (bits x (if (< i (+ m n))
                                        (- i n)
                                      (1- m)) 0)
                            (+ 1 (- i n))
                            (bits y (1- n) j)
                            (- n j))))))
  :hints (("Goal" :in-theory (enable bits-cat-1
                                     bits-cat-2
                                     bits-cat-3))))

;The following trivial corollary of bits-cat is worth keeping enabled.

(defthm bits-cat-constants
  (implies (and (syntaxp (quotep n))
                (syntaxp (quotep m))
                (syntaxp (quotep i))
                (syntaxp (quotep j))
                (natp n)
                (natp m)
                (natp i)
                (natp j))
           (equal (bits (cat x m y n) i j)
                  (if (< i n)
                      (bits y i j)
                    (if (>= j n)
                        (bits x (if (< i (+ m n))
                                    (- i n)
                                  (1- m))
                              (- j n))
                      (cat (bits x (if (< i (+ m n))
                                       (- i n)
                                     (1- m)) 0)
                           (+ 1 (- i n))
                           (bits y (1- n) j)
                           (- n j)))))))

;bitn-cat should be all we need for simplifying (bitn (cat...))
(defthmd bitn-cat-1
  (implies (and (< i n)
                (case-split (natp n))
                (case-split (natp m))
                (case-split (natp i))
                )
           (equal (bitn (cat x m y n) i)
                  (bitn y i)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn bits-cat-1)
                              '()))))

;bitn-cat should be all we need for simplifying (bitn (cat...))
(defthmd bitn-cat-2
  (implies (and (>= i n)
                (case-split (natp n))
                (case-split (natp m))
                (case-split (integerp i))
                )
           (equal (bitn (cat x m y n) i)
                  (if (< i (+ m n))
                      (bitn x (- i n))
                    0)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn)
                              '()))))

;includes both bitn-cat-1 and bitn-cat-2
(defthm bitn-cat
  (implies (and (case-split (natp n))
                (case-split (natp m))
                (case-split (natp i)))
           (equal (bitn (cat x m y n) i)
                  (if (< i n)
                      (bitn y i)
                    (if (< i (+ m n))
                      (bitn x (- i n))
                    0))))
  :hints (("Goal" :in-theory (enable bitn-cat-1
                                     bitn-cat-2))))

;The following trivial corollary of bitn-cat is worth keeping enabled.

(defthm bitn-cat-constants
  (implies (and (syntaxp (quotep n))
                (syntaxp (quotep m))
                (syntaxp (quotep i))
                (natp n)
                (natp m)
                (natp i))
           (equal (bitn (cat x m y n) i)
                  (if (< i n)
                      (bitn y i)
                    (if (< i (+ m n))
                      (bitn x (- i n))
                    0)))))

(defthm cat-bits-bits
  (implies (and (equal j (1+ k))
                (equal n (+ 1 (- l) k))
                (case-split (<= (+ 1 (- j) i) m))
                (case-split (<= j i))
                (case-split (<= l k))
                (case-split (integerp i))
                (case-split (integerp k))
                (case-split (integerp l))
                (case-split (integerp m))
                )
           (equal (cat (bits x i j) m (bits x k l) n)
                  (bits x i l)))
  :hints (("Goal" :in-theory (enable cat)
           :use ((:instance bits-plus-bits (n i) (p j) (m l))))))

(defthm cat-bitn-bits
    (implies (and (equal j (+ 1 k))
		  (equal n (+ 1 (- l) k))
                  (case-split (<= 1 m))
		  (case-split (<= l k))
		  (case-split (integerp j))
                  (case-split (integerp k))
                  (case-split (integerp l))
                  (case-split (integerp m))
		  )
	     (equal (cat (bitn x j) m (bits x k l) n)
		    (bits x j l)))
    :hints (("Goal" :in-theory (enable bitn))))

(defthm cat-bits-bitn
  (implies (and (equal j (+ 1 k))
                (case-split (<= (+ 1 (- j) i) m))
                (case-split (<= j i))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp m))
                )
           (equal (cat (bits x i j) m (bitn x k) 1)
                  (bits x i k)))
  :hints (("Goal" :in-theory (enable bitn))))

(defthm cat-bitn-bitn
  (implies (and (equal i (+ 1 j))
                (case-split (integerp i))
                (case-split (integerp j)))
           (equal (cat (bitn x i) 1 (bitn x j) 1)
                  (bits x i j)))
  :hints (("Goal" :in-theory (enable bitn))))




;may not want this enabled (but probably do want CAT-EQUAL-CONSTANT enabled)
;the BITS calls around X and Y in the conclusion allow us to drop the hyps that X and Y are bvecps.
(defthmd cat-split-equality
  (implies (and (case-split (bvecp k (+ m n))) ;if not, K can't be equal to the CAT expression
                (case-split (integerp m))
                (case-split (<= 0 m))
                (case-split (integerp n))
                (case-split (<= 0 n))
                )
           (equal (equal k (cat x m y n))
                  (and (equal (bits y (1- n) 0) (bits k (1- n) 0))
                       (equal (bits x (1- m) 0) (bits k (+ -1 m n) n)))))
  :hints (("Goal" :in-theory (enable cat-ignores-bits)
           :use ((:instance cat-bits-bits (x  (cat x m y n)) (i (+ -1 m n)) (j n) (k (+ -1 n)) (l 0))))))



;generalize this by dropping the bvecp-hyps and wrapping bits around x and y in the conclusion?
;follows trivially from   cat-split-equality
;prove a version of this without the bvecp hyps?
(defthm cat-equal-constant
  (implies (and (syntaxp (and (quotep k)
                              (quotep m)
                              (quotep n)))
                (case-split (bvecp y n))
                (case-split (bvecp x m))
                (case-split (< k (expt 2 (+ m n)))) ;drop!
                (case-split (integerp k))
                (case-split (<= 0 k))
                (case-split (integerp m))
                (case-split (<= 0 m))
                (case-split (integerp n))
                (case-split (<= 0 n))
                )
           (equal (equal k (cat x m y n))
                  (and (equal y (bits k (1- n) 0))
                       (equal x (bits k (+ -1 m n) n)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable cat-split-equality))))

;lacks the bvecp hyps.  do we want this or cat-equal-rewrite?
(defthm cat-equal-rewrite-alt
  (implies (and (case-split (natp n))
                (case-split (natp m))
                )
           (equal (equal (cat x1 m y1 n)
                         (cat x2 m y2 n))
                  (and (equal (bits x1 (1- m) 0) (bits x2 (1- m) 0))
                       (equal (bits y1 (1- n) 0) (bits y2 (1- n) 0)))))
  :hints (("Goal" :in-theory (enable cat-split-equality))))

;move hyps to conclusion?
(defthm cat-equal-rewrite
  (implies (and (case-split (bvecp x1 m))
                (case-split (bvecp y1 n))
                (case-split (bvecp x2 m))
                (case-split (bvecp y2 n))
                (case-split (integerp n))
                (case-split (<= 0 n))
                (case-split (integerp m))
                (case-split (<= 0 m))
                )
           (equal (equal (cat x1 m y1 n)
                         (cat x2 m y2 n))
                  (and (equal x1 x2)
                       (equal y1 y2))))
  :hints (("Goal" :in-theory (enable cat-split-equality))))

(defthm cat-bits-bits-bits
  (implies (and (<= k i)
                (<= l k)
                (<= j l)
                (integerp i)
                (integerp j)
                (integerp k)
                (integerp l)
                )
           (equal (cat (bits x i (+ 1 k))
                       (+ 2 i (- k))
                       (cat (bits x k l)
                            (+ 1 k (- l))
                            (bits x (1- l) j)
                            (+ l (- j)))
                       (+ 1 (- j) k))
                  (bits x i j)))
  :rule-classes nil)

#|
bits-dont-match can prove things like this:
(thm (IMPLIES (EQUAL 7 (BITS x 8 6))
              (NOT (EQUAL 3 (BITS x 15 6)))))
|#

(defthm bits-dont-match
  (implies (and (syntaxp (and (quotep i)
                              (quotep j)
                              (quotep k)))
                (equal (bits x i2 j2) k2) ;i2, j2, and k2 are free vars
                (syntaxp (and (quotep i2)
                              (quotep j2)
                              (quotep k2)))
                (<= j2 j) (<= j i) (<= i i2)
                (not (equal k (bits k2 (+ i (- j2)) (+ (- j2) j))))
                (<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
                (integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2)
                )
           (equal (equal k (bits x i j))
                  nil))
  :otf-flg t
  :hints (("Goal" :in-theory ( set-difference-theories
                               (enable)
                              '( cat-bits-bits))
           :use (:instance cat-bits-bits-bits
                           (i i2)
                           (j j2)
                           (k (+ i (- j2)))
                           (l (+ j (- j2)))))))

(defthm bits-match
  (implies (and (syntaxp (and (quotep i)
                              (quotep j)
                              (quotep k)))
                (equal (bits x i2 j2) k2) ;i2, j2, and k2 are free vars
                (syntaxp (and (quotep i2)
                              (quotep j2)
                              (quotep k2)))
                (<= j2 j) (<= j i) (<= i i2)
                (equal k (bits k2 (+ i (- j2)) (+ (- j2) j)))
                (<= 0 i) (<= 0 j) (<= 0 k) (<= 0 i2) (<= 0 j2) (<= 0 k2)
                (integerp i) (integerp j)  (integerp k) (integerp i2) (integerp j2) (integerp k2)
                )
           (equal (equal k (bits x i j))
                  t))
  :otf-flg t
  :hints (("Goal" :in-theory ( set-difference-theories
                               (enable)
                              '( cat-bits-bits))
           :use (:instance cat-bits-bits-bits
                           (i i2)
                           (j j2)
                           (k (+ i (- j2)))
                           (l (+ j (- j2)))))))


;make into a rewrite rule
(defthm cat-with-slice-of-x-equal-x
  (implies (and (bvecp x (+ m n))
                (case-split (bvecp y n))
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (equal (equal x (cat (bits x (+ -1 m n) n) m y n))
                  (equal (bits x (1- n) 0) y))
           )
  :hints (("Goal" :in-theory (disable CAT-BITS-BITS
                                      BITS-SPLIT-AROUND-ZERO)
           :use (:instance cat-bits-bits (i (+ -1 m n)) (l 0) (j n) (k (+ -1 n))))))

;cat-with-slice-of-x-equal-x won't match, so we use kk here
;add a syntaxp hyp?
(defthm cat-with-slice-of-x-equal-x-rewrite
  (implies (and (equal kk (+ -1 m n))
                (bvecp x (+ m n))
                (case-split (bvecp y n))
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (equal (equal x (cat (bits x kk n) m y n))
                  (equal (bits x (1- n) 0) y))
           )
  :hints (("Goal" :in-theory (disable CAT-BITS-BITS
                                      BITS-SPLIT-AROUND-ZERO)
           :use (:instance cat-bits-bits (i (+ -1 m n)) (l 0) (j n) (k (+ -1 n))))))

;If X and Y have identical bits in the range [i..j], then they also match on any subrange [k..l] of [i..j]
(defthmd bits-equal-implies-subranges-equal-helper
  (implies (and (equal (bits x i j) (bits y i j))
                (<= j l)
                (<= k i)
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp l))
                )
           (equal (equal (bits x k l) (bits y k l))
                  t))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :in-theory (disable cat-bits-bits cat-equal-rewrite cat-equal-rewrite-alt)
           :use ((:instance cat-equal-rewrite
                            (x1 (BITS X K L))
                            (y1 (BITS X (+ -1 L) J))
                            (x2 (BITS Y K L))
                            (y2 (BITS Y (+ -1 L) J))
                            (m (+ 1 k (* -1 l)))
                            (n (+ L (* -1 J))))
                 (:instance cat-equal-rewrite
                            (x1 (BITS X I (+ 1 K)))
                            (y1 (CAT (BITS X K L)
                                     (+ 1 k (* -1 l))
                                     (BITS X (+ -1 L) J)
                                     (+ L (* -1 J))))
                            (x2 (BITS Y I (+ 1 K)))
                            (y2 (CAT (BITS Y K L)
                                      (+ 1 k (* -1 l))
                                     (BITS Y (+ -1 L) J)
                                     (+ L (* -1 J))))
                            (m (+ 2 i (* -1 k)))
                            (n (+ 1 K (* -1 J))))
                 (:instance cat-bits-bits-bits (x x))
                 (:instance cat-bits-bits-bits (x y)))
           )))

(defthm bits-equal-implies-subranges-equal
  (implies (and (equal (bits x i j) (bits y i j))
                (<= j l)
                (<= k i)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (equal (bits x k l) (bits y k l))
                  t))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :use ( bits-equal-implies-subranges-equal-helper)
           )))


#|

(thm
 (implies (and (integerp m) (integerp n) (<= 0 m) (<= 0 n) (bvecp x m)
                (bvecp y n))
          (equal (EQUAL (BINARY-CAT X M Y N) X)
                 (or (equal y 0) (equal n 0))))
 :hints (("Goal" :in-theory (enable binary-cat bvecp))))

;keep disabled?
(defthm cat-when-bits-of-x-are-0
  (implies (and (EQUAL (BITS X (1- M) 0) 0)
                (integerp m)
                (<= 0 m))
           (equal (cat x m y n)
                  (bits y (+ -1 n) 0))))
|# ; |
