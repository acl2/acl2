(in-package "ACL2")

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

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

(local (include-book "../arithmetic/top"))

(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defund expo (x)
  (declare (xargs :guard t
                  :measure (expo-measure x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
	((< x 0) (expo (- x)))
	((< x 1) (1- (expo (* 2 x))))
	((< x 2) 0)
	(t (1+ (expo (/ x 2))))))



(include-book "../arithmetic/negative-syntaxp")
(include-book "../arithmetic/power2p")

(local (include-book "ground-zero"))

(local (include-book "bits"))
(local (include-book "bvecp")) ;to get bvecp-longer

;(in-theory (disable expt-inverse))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defthm bitn-nonnegative-integer
  (and (integerp (bitn x n))
       (<= 0 (bitn x n)))
  :hints (("Goal" :in-theory (enable bitn)))
  :rule-classes (:type-prescription))

(defthm bitn-with-n-not-an-integer
  (implies (not (integerp n))
           (equal (bitn x n)
                  0))
  :hints (("Goal" :in-theory (enable bitn))))


(encapsulate
 ()
;gen
 (local (defthm bitn-upper-bound-case-1
          (implies (integerp n)
                   (<= (bitn x n) 1))
          :otf-flg t
          :hints (("Goal" :use (:instance fl-def-linear-part-2 (x (* 1/2 X (/ (EXPT 2 N)))))
                   :in-theory (set-difference-theories
                               (enable mod bitn bits expt-split)
                               '( fl-def-linear-part-2
                                  a10
;                          REARRANGE-ERIC-4
;                                  REARRANGE-FRACTIONAL-COEFS-<
                                  ))))
          :rule-classes (:rewrite :linear)))
;separate out the linear rule?

 (local (defthm bitn-upper-bound-case-2
          (implies (not (integerp n))
                   (<= (bitn x n) 1))
          :otf-flg t
          :hints (("Goal" :cases ((integerp (+ n 1)))
                   :in-theory (set-difference-theories
                               (enable mod bitn bits expt-split)
                               '(A10
                                 fl-def-linear-part-2
 ;                                REARRANGE-FRACTIONAL-COEFS-<
                                 ))))
          :rule-classes (:rewrite :linear)))



 (defthm bitn-upper-bound
   (<= (bitn x n) 1)
   :hints (("Goal" :cases ((integerp n)))))
 )

(defthm bitn-upper-bound-linear
  (<= (bitn x n) 1)
  :rule-classes ((:LINEAR :TRIGGER-TERMS ((bitn x n)))))

;!! was looping with expt-compare
; look into this more
(local (in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND)))

(encapsulate
 ()
;derive from bits-minus?
 (local (defthm bitn-minus-case-1
          (implies (and (rationalp x)
                        (integerp n)
                        (integerp (/ x (expt 2 (+ 1 n))))
                        )
                   (equal (bitn (* -1 x) n)
                          (- (bitn x n))
                          ))
          :hints (("Goal" :in-theory (set-difference-theories
                                      (enable bitn
                                              bits
                                              mod-cancel
                                              expt-minus
                                              expt-split)
                                      '( ;expt-inverse
                                        ))))))


 (local (defthm bitn-minus-case-2
          (implies (and (rationalp x)
                        (integerp n)
                        (not (integerp (/ x (expt 2 n))))
                        )
                   (equal (bitn (* -1 x) n)
                          (- 1 (bitn x n))
                          ))
          :hints (("Goal" :in-theory (set-difference-theories
                                      (enable bitn
                                              mod
                                              mod-cancel
                                              bits
                                              even-int-implies-int
                                              expt-minus
                                              expt-split)
                                      '( ;expt-inverse
                                        ))))))


 (local (defthm bitn-minus-case-3
          (implies (and (rationalp x)
                        (integerp n)
                        (not (integerp (/ x (expt 2 (+ 1 n)))))
                        (integerp (/ x (expt 2 n)))
                        )
                   (equal (bitn (* -1 x) n)
                          (- 2 (bitn x n))
                          ))
          :hints (("Goal" :in-theory (set-difference-theories
                                      (enable bitn
                                              mod
                                              mod-cancel
                                              bits
                                              expt-minus
                                              expt-split)
                                      '( ;expt-inverse
                                        ))))))





 (defthm bitn-minus
   (implies (and (syntaxp (negative-syntaxp x))
                 (case-split (rationalp x)) ;gen?
                 (case-split (integerp n))
                 )
            (equal (bitn x n)
                   (if (integerp (/ x (expt 2 (+ 1 n))))
                       (- (bitn (- x) n))
                     (if (integerp (/ x (expt 2 n)))
                         (- 2 (bitn (- x) n))
                       (- 1 (bitn (- x) n))))))))



;(in-theory (disable  FL-EQUAL-0))

;1 rewrite to odd?
(defthm bitn-0-rewrite-to-even
  (implies (integerp x)
           (equal (equal (bitn x 0) 0)
                  (integerp (* 1/2 x))))
  :hints (("Goal" :in-theory (enable bitn bits  mod-by-2-rewrite-to-even)))
  )


;...


;(in-theory (disable  bitn-sum-lowbits)) ;was causing loops


;this one should remain last? <-- huh?
(theory-invariant (incompatible (:rewrite bits-n-n-rewrite)
                                (:definition bitn)
                                )
                  :key bitn-and-bits-n-n-shouldnt-alternate)

(defthmd bits-n-n-rewrite
  (equal (BITS X n n)
         (bitn x n))
  :hints (("Goal" :in-theory (enable bitn)))
  )




#|
;should only fire if it really does simplify x, that is, if x really has bits to be dropped
(defthm bitn-sum-simplify-first-term
  (implies (and (>= (abs x) (expt 2 (+ n 1))) ;prevents loop
                (rationalp x)
                (rationalp y)
                (integerp n))
           (equal (bitn (+ x y) n)
                  (bitn (+ (lowbits x n) y) n)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable
                               lowbits
                               bitn bits)
                              '()))))

;should only fire if it really does simplify y, that is, if y really has bits to be dropped
(defthm bitn-sum-simplify-second-term
  (implies (and (>= (abs y) (expt 2 (+ n 1))) ;prevents loop
                (rationalp x)
                (rationalp y)
                (integerp n))
           (equal (bitn (+ x y) n)
                  (bitn (+ x (lowbits y n)) n)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable lowbits
                                      bitn bits)
                              '()))))

(defthm bitn-sum-simplify-third-term
  (implies (and (>= (abs z) (expt 2 (+ n 1))) ;prevents loop
                (rationalp x)
                (rationalp y)
                (rationalp z)
                (integerp n))
           (equal (bitn (+ x y z) n)
                  (bitn (+ x y (lowbits z n)) n)))
  :hints (("Goal" :in-theory (disable bitn-sum-simplify-first-term
                                      bitn-sum-simplify-second-term)
           :use (:instance bitn-sum-simplify-first-term (x z) (y (+ x y))))))



|#


(defthm bitn-upper-bound-2
  (< (bitn x n) 2)
  :hints (("Goal" :in-theory (disable  bitn-upper-bound)
           :use  bitn-upper-bound)))

(defthm bitn-0-1
  (or (equal (bitn x n) 0)
      (equal (bitn x n) 1))
  :hints (("Goal" :in-theory (disable bitn)))
  :rule-classes nil)


;my strategey with the rules below is to rewrite prefer (not (equal (bitn x n) 0)) over (equal (bitn x n) 1)
;this allows subsumption to ...

;bad to have both?
(defthm bitn-not-0-means-1
  (equal (not (equal (bitn x n) 0))
         (equal (bitn x n) 1))
  :hints (("Goal" :use bitn-0-1)))

(defthm bitn-not-1-means-0
  (equal (not (equal (bitn x n) 1))
         (equal (bitn x n) 0))
  :hints (("Goal" :use bitn-0-1)))

;these are bad rules?
(in-theory (disable bitn-not-1-means-0 bitn-not-0-means-1))

;add matt's forward chaining rules for dealing with single bits (maybe they should go in bvecp.lisp)


(encapsulate
 ()
 (local (defthm bitn-bitn-case-1
          (implies (case-split (integerp n))
                   (equal (bitn (bitn x n) 0)
                          (bitn x n)))
          :hints (("Goal"
                   :in-theory (set-difference-theories
                               (enable bitn bits)
                               '())))))


 (local (defthm bitn-bitn-case-2
          (implies (not (integerp n))
                   (equal (bitn (bitn x n) 0)
                          (bitn x n)))
          :hints (("Goal" :cases ((acl2-numberp n))
                   :in-theory (set-difference-theories
                               (enable bitn bits mod)
                               '())))))

 (defthm bitn-bitn
   (equal (bitn (bitn x n) 0)
          (bitn x n))))



;bb
(defthm bitn-known-not-0-replace-with-1
  (implies (not (equal (bitn x n) 0)) ; backchain-limit?
           (equal (bitn x n)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :use (:instance bitn-0-1)))
  )



;needed?
(defthm bitn->-0
  (equal (< 0 (bitn x n))
         (not (equal 0 (bitn x n)))))

(defthm bitn-<-1
  (equal (< (BITN X n) 1)
         (equal (BITN X n) 0))
  :hints (("Goal"
           :use bitn-0-1)))

;useful if bitn-upper-bound and bitn-upper-bound-2 are disabled
(defthm bitn-not->-1
  (implies (and (syntaxp (quotep k))
                (<= 1 k))
           (equal (< k (bitN x n))
                  nil))
  :hints (("Goal" :in-theory (disable bitn-upper-bound bitn-upper-bound-2)
           :use bitn-upper-bound)))


;useful if bitn-upper-bound and bitn-upper-bound-2 are disabled
(defthm bitn-<=-1
  (implies (and (syntaxp (quotep k))
                (< 1 k))
           (equal (< (bitN x n) k)
                  t))
    :hints (("Goal" :in-theory (disable  BITN-NOT->-1 bitn-upper-bound bitn-upper-bound-2)
           :use bitn-upper-bound)))

#|
;cc
(defthm bitn-shift-alt
  (implies (and (syntaxp (should-have-a-2-factor-divided-out x))
                (> n 0) ;restricts application
                (rationalp x)
                (integerp n)
                )
           (equal (bitn x n)
                  (bitn (/ x 2) (- n 1))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bits bitn)
                              '(bits-shift-alt
                                ))
           :use (:instance bits-shift-alt (i n) (j n)))))
|#

(defthmd bitn-def
  (implies (case-split (integerp k))
           (equal (bitn x k)
                  (mod (fl (/ x (expt 2 k)))
                       2)))
  :hints (("Goal" :in-theory (enable bits bitn expt-split))))



(defun not-eric (x)
  (if (equal x 0)
      1
    0))



#|
;this does most of the work (i.e., it gets the constant below 2^i+1
(defthm bitn-sum-lowbits
  (implies (and (syntaxp (and (quotep x) (>= (cadr x) (expt 2 (+ 1 (cadr n)))))) ;dropped negative case
                (rationalp x)
                (rationalp y)
                (integerp n)
                )
           (equal (bitn (+ x              y) n)
                  (bitn (+ (lowbits x n) y) n)))
  :hints (("Goal" :in-theory (enable bitn)
           :use  (:instance bits-sum-lowbits (i n) (j n) ))))
|#

(defthm bitn-drop-crucial-bit-and-flip-result
  (implies (and (case-split (rationalp x))
                (case-split (integerp n)) ;drop?
                )
           (and (equal (bitn (+ (expt 2 n) x) n)
                       (not-eric (bitn x n)))
                (equal (bitn (+ x (expt 2 n)) n)
                       (not-eric (bitn x n)))))
  :otf-flg t
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bits bitn-def
                                      expt-split
                                      )
                              '(
                                MOD-PULL-INSIDE-FL-SHIFT-ALT-ALT-ALT-ALT
                                floor-fl)))))

(defthm bitn-drop-crucial-bit-and-flip-result-alt-gen
  (implies (and (syntaxp (and (quotep j)
                              (< (cadr j) (expt 2 (+ 1 (cadr n)))) ;bitn-sum-lowbits does most of the work
                              (>= (cadr j) (expt 2 (cadr n)))))
                (rationalp j)
                (rationalp x)
                (integerp n)
                )
           (equal (bitn (+ j x) n)
                  (not-eric (bitn (+ (- j (expt 2 n)) x) n))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable bitn-drop-crucial-bit-and-flip-result)
           :use (:instance bitn-drop-crucial-bit-and-flip-result (x (+ j (- (expt 2 n)) x))))))

;for negative constants j
;might be slow if the negative constant has a large absolute value
;make a negative version of bitn-sum-lowbits
(defthm bitn-add-crucial-bit-and-flip-result
  (implies (and (syntaxp (and (quotep j)
                              (quotep n)
                              (< (cadr j) 0)))
                (rationalp j)
                (rationalp x)
                (integerp n)
                )
           (equal (bitn (+ j x) n)
                  (not-eric (bitn (+ (+ j (expt 2 n)) x) n))))
  :otf-flg t
  :hints (("Goal" :in-theory (disable  bitn-drop-crucial-bit-and-flip-result)
           :use (:instance bitn-drop-crucial-bit-and-flip-result (x (+ j  x))))))



(defthm bitn-equal-to-silly-value
  (implies (and (syntaxp (quotep k))
                (not (or (equal 0 k) (equal 1 k)))
                )
           (equal (equal k (bitn x n))
                  nil)))




(defthm bitn-split-around-zero
  (implies (and (<= (- (expt 2 n)) x)
                (< x (expt 2 n))
                (rationalp x)
                (integerp n)
                )
           (equal (equal (bitn x n) 0)
                  (<= 0 x)))
  :otf-flg t
  :hints (("Goal" :cases ((<= 0 x))
           :in-theory (enable bitn bits expt-split  mod-force-chosen-a-neg)))
  )


;drop silly hyps like: (<= -128 (BITN FOO 24))
(defthm bitn-drop-silly-bound
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                )
  (equal (< (bitn x n) k)
         nil)))

(defthm bitn-drop-silly-bound-2
  (implies (and (syntaxp (quotep k))
                (< k 0)
                )
  (equal (< k (bitn x n))
         t)))


(defthm bitn-even-means-0
  (equal (INTEGERP (* 1/2 (BITN x n)))
         (equal (bitn x n) 0)))

;new - export disabled?
(defthm bitn-too-small
  (implies (and (< x (expt 2 n))
                (<= 0 x) ;case-split?
                )
           (equal (bitn x n)
                  0))
  :hints (("Goal" :cases ((rationalp x)) ;why needed?
           :in-theory (enable bitn bits expt-split)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil)))
  )

(defthm bitn-normal-form
  (equal (equal (bitn x n) 1)
         (not (equal (bitn x n) 0))))


(defthm bitn-of-non-rational
  (implies (not (rationalp x))
           (equal (bitn x n)
                  0))
  :hints (("Goal" :in-theory (enable bitn)))
)






(encapsulate
 ()
 (local (defthm bitn-bvecp-simple
   (bvecp (bitn x n) 1)
   :hints (("Goal" :use bitn-0-1
            :in-theory (set-difference-theories
                        (enable bvecp)
                        '()
                        )))))

 (defthm bitn-bvecp
   (implies (and (<= 1 k)
                 (case-split (integerp k)))
            (bvecp (bitn x n) k))
   :hints (("Goal" :use  bitn-bvecp-simple
            :in-theory (disable bitn-bvecp-simple
                              ))))
 )

(defthm bitn-times-fraction-integerp
  (implies (and (not (integerp k))
                (case-split (acl2-numberp k))
                )
           (equal (INTEGERP (* k (BITN x n)))
                  (equal (BITN x n) 0))))



(defthm bitn-in-product-split-cases
  (and (implies (case-split (acl2-numberp k))
                (equal (* (bitn x n) k)
                       (if (equal (bitn x n) 0)
                           0
                         k)))
       (implies (case-split (acl2-numberp k))
                (equal (* k (bitn x n))
                       (if (equal (bitn x n) 0)
                           0
                         k)))))
;(in-theory (disable bitn-in-product-split-cases))

(defthm bitn-in-sum-split-cases
  (and (implies (case-split (acl2-numberp k))
                (equal (+ k (bitn x n))
                       (if (equal (bitn x n) 0)
                           k
                         (+ k 1))))

       (implies (case-split (acl2-numberp k))
                (equal (+ (bitn x n) k)
                       (if (equal (bitn x n) 0)
                           k
                         (+ k 1))))))
;(in-theory (disable bitn-in-sum-split-cases))

#|
(defthm bitn-shift-better
  (implies (and (bind-free (can-take-out-numeric-power-of-2 x) (c))
                (force (power2p c))
                (case-split (integerp n))
                )
           (equal (bitn x n)
                  (bitn (/ x c) (- n (expo c)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn)
                              '(bits-shift-better)
                              )
           :use (:instance bits-shift-better (i n) (j n)))))

|#

(defthm bitn-0
  (equal (bitn 0 k)
         0)
  :hints (("goal" :in-theory (enable bitn))))

;may cause case splits (maybe that's good?)
(defthm bitn-expt-gen
  (implies (case-split (integerp i))
           (equal (bitn (expt 2 i) n)
                  (if (equal i n)
                      1
                    0)))
  :hints (("Goal" :in-theory (enable bitn))))

(defthmd bitn-expt
  (implies (case-split (integerp n))
           (equal (bitn (expt 2 n) n) 1)))

;These are intended for the (perhaps weird) case when x in (bitn x n) is a constant but n is not a constant.
;I actually had this term in a proof: (EQUAL (BITN 128 (BITS <signal-name> 8 6)) 0)

(defthm bitn-of-expt-equal-0
  (implies (and (syntaxp (quotep x))
                (equal x (expt 2 (expo x))) ;means x is a power of 2
                )
           (equal (equal (bitn x n) 0)
                  (not (equal n (expo x))))));note that (expo x) will be a constant since x is

(defthm bitn-of-expt-equal-1
  (implies (and (syntaxp (quotep x))
                (equal x (expt 2 (expo x))) ;means x is a power of 2
                )
           (equal (equal (bitn x n) 1)
                  (equal n (expo x))))) ;note that (expo x) will be a constant since x is

#|
(defthm bitn-of-expt-constant
  (implies (and (syntaxp (quotep x))
                (equal e (expo x)) ;having E means we don't have to evaluate (expo x) in the conclusion
                (equal x (expt 2 e)) ;means x is a power of 2
                )
           (equal (bitn x n)
                  (log= n e)))) ;note that e will be a constant

|#

;This is the rule Doc is allowing in lib/, since it doesn't cause as many case-splits are bitn-expt-gen?
(defthmd bitn-expt-0
  (implies (and (not (equal i n))
		(case-split (integerp i)))
	   (equal (bitn (expt 2 i) n) 0)))

(defthm bitn-0-1
    (or (equal (bitn x n) 0)
        (equal (bitn x n) 1))
  :rule-classes ()
  :hints (("goal" :in-theory (enable bitn))))

(defthmd bitn-shift-eric
  (implies (and (integerp n)
                (integerp k)
                )
           (equal (bitn (* x (expt 2 k)) n)
                  (bitn x (+ n (- k)))))
  :hints (("Goal" :in-theory (enable bitn))))

;BOZO replace with bitn-shift-eric ??
(defthmd bitn-shift
  (implies (and (integerp n)
                (integerp k)
                )
           (equal (bitn (* x (expt 2 k)) (+ n k))
                  (bitn x n)))
  :hints (("Goal" :in-theory (enable bitn))))

;gen!
;dammit, ACL2 unifies 0 with (* 2 x), so this rule can loop!
(defthm bitn-shift-by-2
  (implies (and (syntaxp (not (quotep x)))
                (acl2-numberp n))
           (equal (BITN (* 2 x) n)
                  (bitn x (1- n))))
  :hints (("Goal" :use (:instance bitn-shift-eric (k 1))))
  )

(defthmd bitn-plus-mult
  (implies (and (< n m)
                (integerp m)
                (integerp k)
                )
           (equal (bitn (+ x (* k (expt 2 m))) n)
                  (bitn x n)))
  :hints (("Goal" :in-theory (enable bitn bits-plus-mult-2))))

(defthmd bitn-plus-mult-rewrite
    (implies (and (syntaxp (quotep c))
		  (equal (mod c (expt 2 (1+ n))) 0))
	     (equal (bitn (+ c x) n)
		    (bitn x n)))
    :hints (("Goal" :use ((:instance bitn-plus-mult
                                     (x x)
                                     (k (/ c (expt 2 (1+ n))))
                                     (m (1+ n))
                                     (n n)))
             :in-theory (enable mod))))

;we almost always want to leave this disabled!
(defthmd bitn-plus-bits
  (implies (and (<= m n)
                (integerp m)
                (integerp n)
                )
           (= (bits x n m)
              (+ (* (bitn x n) (expt 2 (- n m)))
                 (bits x (1- n) m))))
  :hints (("goal" :in-theory (enable bitn)
           :use ((:instance bits-plus-bits (n n) (p n) (m m)))
           )))

;we almost always want to leave this disabled!
(defthm bits-plus-bitn
    (implies (and (<= m n)
                  (integerp m)
		  (integerp n)
		  )
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable bitn)
           :use ((:instance bits-plus-bits (n n) (m m) (p (+ m 1)))))))

;drop?
(defthm bits-0-bitn-0
  (implies (and (<= 0 n)
                (integerp n)
                )
           (iff (= (bits x n 0) 0)
                (and (= (bitn x n) 0)
                     (= (bits x (1- n) 0) 0))))
  :rule-classes ()
  :hints (("Goal" :use (:instance bitn-plus-bits (m 0)))))

(defthmd bitn-shift-2
  (implies (and (<= 0 k)
                (integerp k)
                (integerp r)
                )
           (equal (bitn (fl (/ x (expt 2 r))) k)
                  (bitn x (+ k r))))
  :hints (("goal" :in-theory (e/d (bits-shift-down bitn) (BITS-FL)))))

(defthm bitn-shift-by-constant-power-of-2
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (case-split (integerp n))
                )
           (equal (bitn (* k x) n)
                  (bitn x (- n (expo k)))))
  :hints (("Goal" :use (:instance  bits-shift-by-constant-power-of-2 (i n) (j n))
           :in-theory (enable bitn))))

(defthmd bitn-shift-eric-2
  (implies (and (integerp n)
                (integerp k)
                )
           (equal (bitn (* (expt 2 k) x) n) ;BOZO rewrite the (+ n k) to match better
                  (bitn x (+ n (- k)))))
  :hints (("Goal" :in-theory (enable bitn))))



(defthmd bitn-rec-0
  (implies (integerp x)
           (equal (bitn x 0)
                  (mod x 2)))
  :hints (("goal" :use ((:instance bitn-def (k 0))))))

;rename?
;is there a bits analog of this theorem?
;move or copy to bitn?
;change k to n
;BOZO change formal k to n
(defthmd bitn-rec-pos
  (implies (< 0 k) ;k cannot be 0 or negative
           (equal (bitn x k)
                  (bitn (fl (/ x 2)) (1- k))))
  :rule-classes ((:definition :controller-alist ((bitn t t))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable bitn-def expt-split)
                              '( ; bitn-def
                                fl/int-rewrite
                                fl-shift-fl
                                mod-pull-inside-fl-shift-alt-alt-alt
                                mod-pull-inside-fl-shift-alt-alt-alt-alt))
           :use ((:instance fl/int-rewrite (x (/ x 2)) (n (expt 2 (1- k))))))))



;generalize to bits-mod?
(defthmd bitn-mod
  (implies (and (< k n)
                (integerp n)
                (integerp k)
                )
           (equal (bitn (mod x (expt 2 n)) k)
                  (bitn x k)))
  :hints (("Goal"; :cases ((integerp n))
           :in-theory (enable bitn bits))))

;dup?
(defthm BIT-EXPO-A
  (implies (and (< x (expt 2 n))
                (>= x 0)
                (integerp n)
                )
           (equal (bitn x n) 0))
  :rule-classes ())

;special case of  bit-expo-c?
(defthm BIT-EXPO-B
  (implies (and (<= (expt 2 n) x)
                (< x (expt 2 (1+ n)))
                (rationalp x)
                (integerp n)
                ;(>= x 0)
                ;(>= n 0)
                )
           (equal (bitn x n) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expt-split bitn-def)
           :use ((:instance fl-unique (x (/ x (expt 2 n))) (n 1))))))

(defthm bitn-plus-expt-1
  (implies (and (rationalp x)
                (integerp n)
                )
           (not (equal (bitn (+ x (expt 2 n)) n)
                       (bitn x n))))
  :rule-classes ()
)


;bozo. dup?
;prove from bitn-plus-mult?
(defthm bitn-plus-expt-2
  (implies (and (< n m)
                (integerp n)
                (integerp m)
                )
           (equal (bitn (+ x (expt 2 m)) n)
                  (bitn x n)))
  :hints (("Goal" :in-theory (enable bitn))))

;this is the most interesting case. perhaps add the other cases for k<0 and k>i-j
(defthm bitn-bits
  (implies (and (<= k (- i j))
                (case-split (<= 0 k))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                )
           (equal (bitn (bits x i j) k)
                  (bitn x (+ j k))))
  :hints (("Goal" :in-theory (e/d ( bitn) (BITS-FL)))))

;The following trivial corollary of bitn-bits is worth keeping enabled.

(defthm bitn-bits-constants
  (implies (and (syntaxp (quotep i))
                (syntaxp (quotep j))
                (syntaxp (quotep k))
                (<= k (- i j))
                (<= 0 k)
                (integerp i)
                (integerp j)
                (integerp k))
           (equal (bitn (bits x i j) k)
                  (bitn x (+ j k)))))


(defthmd bit+*k-2
  (implies (and (< x (expt 2 m))
                (<= 0 x)
                (rationalp x)
                (<= m n)
                (integerp k)
                (case-split (integerp n))
                (case-split (integerp m))
                )
           (equal (bitn (+ x (* k (expt 2 m))) n)
                  (bitn k (- n m))))
  :hints (("Goal" :in-theory (enable bitn bits+2**k-2))))

(defthmd bitn-shift-3
  (implies (and (bvecp x m)
                (<= m n)
                (integerp k)
                (case-split (integerp n))
                (case-split (integerp m))
                )
           (equal (bitn (+ x (* k (expt 2 m))) n)
                  (bitn k (- n m))))
  :hints (("Goal" :in-theory (enable bvecp)
           :use (bit+*k-2))))


;try

(local
 (defthm bit-expo-c-4
   (implies (and (rationalp x)
                 (integerp n)
                 (integerp k)
                 (<= k n)
                 (< x (expt 2 n))
                 (<= (- (expt 2 n) (expt 2 k)) x))
            (= (fl (/ x (expt 2 k)))
               (1+ (* 2 (1- (expt 2 (1- (- n k))))))))
   :rule-classes ()
   :hints (("goal" :in-theory (set-difference-theories
                               (enable expt-split expt-minus )
                               '())
            :use ((:instance fl-unique (x (/ x (expt 2 k))) (n (1- (expt 2 (- n k))))))))))



(local
 (defthm bit-expo-c-6
   (implies (and (rationalp x)
                 (integerp n)
                 (integerp k)
                 (< k n)
                 (< x (expt 2 n))
                 (<= (- (expt 2 n) (expt 2 k)) x))
            (= (mod (fl (/ x (expt 2 k))) 2)
               1))
   :rule-classes ()
   :hints (("goal" :in-theory (disable  expt-split
                               )
            :use ( ;(:instance bit-expo-c-5)
                         (:instance bit-expo-c-4)
                         (:instance mod-mult-eric (x 1) (y 2) (a (1- (expt 2 (1- (- n k))))))
)))))

;prove this from a more general result about bits??
;BOZO bad name. doesn't mention expo !
(defthm bit-expo-c
    (implies (and (<= (- (expt 2 n) (expt 2 k)) x)
                  (< x (expt 2 n))
                  (< k n)
                  (rationalp x);(integerp x) ;gen more!
		  (integerp n)
		  (integerp k)
		  )
	     (equal (bitn x k) 1))
  :rule-classes ()
  :hints (("goal" :use ((:instance bitn-def)
			(:instance bit-expo-c-6)))))

(defthmd bvecp-bitn-2
    (implies (and (bvecp x n) ; bind free var n here
                  (< k n)
                  (<= (- (expt 2 n) (expt 2 k)) x)
                  (integerp n)
		  (integerp k)
		  )
	     (equal (bitn x k) 1))
    :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :in-theory (enable bvecp)
           :use (bit-expo-c))))

(defthm bitn-bvecp-forward
  (bvecp (bitn x n) 1)
  :rule-classes ((:forward-chaining :trigger-terms ((bitn x n)))))


#| old:
(defun BITN (x n)
  (if (logbitp n x) 1 0))
|#

(defthm bitn-natp
  (natp (bitn x n)))

;BOZO do we want these?
(defthmd bitn-fw-1
  (implies (not (equal (bitn x n) 0))
           (equal (bitn x n) 1)
           )
  :rule-classes (:forward-chaining))

(defthmd bitn-fw-2
  (implies (not (equal (bitn x n) 1))
           (equal (bitn x n) 0)
           )
  :rule-classes (:forward-chaining))

(defthmd bvecp-bitn-0
  (implies (bvecp x n)
           (equal (bitn x n) 0))
  :hints (("Goal" :in-theory (enable bitn bvecp-bits-0))))


;make an alt version?
(defthm bitn-bvecp-0
  (implies (and (bvecp x n)
                (<= 0 m)
                )
           (equal (bitn x (+ m n)) 0))
  :hints (("Goal" :in-theory (disable bvecp-bitn-0)
           :use ((:instance bvecp-bitn-0 (n (+ m n)))))))

;k is a free var
;do we need this, if we have bvecp-longer?
(defthm bitn-bvecp-0-eric
  (implies (and (bvecp x k)
                (<= k n))
           (equal (bitn x n) 0))
  :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :in-theory (enable bvecp-bitn-0))))


;sort of a "bitn-tail" like bits-tail?
(defthm bitn-bvecp-1
    (implies (bvecp x 1)
	     (equal (bitn x 0) x))
    :hints (("Goal" :in-theory (enable bvecp-1-rewrite))))

(defthmd bvecp-bitn-1
    (implies (and (bvecp x (1+ n))
		  (<= (expt 2 n) x)
                  (natp n))
	     (equal (bitn x n) 1))
  :hints (("Goal" :in-theory (enable bvecp)
           :use (bit-expo-b))))

;handle the case where we don't go down to 0?
(defthm bits-bitn
  (implies (and (case-split (integerp i))
                (case-split (<= 0 i))
                )
  (equal (bits (bitn x n) i 0)
         (bitn x n)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bitn)
                              '()))))
