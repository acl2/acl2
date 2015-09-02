(in-package "ACL2")

;(include-book "ground-zero")
(include-book "../arithmetic/power2p")
(include-book "../arithmetic/negative-syntaxp")
(local (include-book "../support/bitn"))
(local (include-book "../support/guards"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; Necessary defuns:

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
                              (natp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

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

;;
;; Begin bitn stuff...
;;

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defthm bitn-with-n-not-an-integer
  (implies (not (integerp n))
           (equal (bitn x n)
                  0)))

(defthm bitn-of-non-rational
  (implies (not (rationalp x))
           (equal (bitn x n)
                  0)))

(defthm bitn-nonnegative-integer
  (and (integerp (bitn x n))
       (<= 0 (bitn x n)))
  :rule-classes (:type-prescription))

;this rule is no better than bitn-nonnegative-integer and might be worse:
(in-theory (disable (:type-prescription bitn)))

(defthm bitn-natp
  (natp (bitn x n)))

(defthm bitn-upper-bound
  (<= (bitn x n) 1))

(defthm bitn-upper-bound-linear
  (<= (bitn x n) 1)
  :rule-classes ((:LINEAR :TRIGGER-TERMS ((bitn x n)))))

;include separate cases?
;BOZO one of the branches simplifies to 0 - see bits-minus
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
                      (- 1 (bitn (- x) n)))))))
;1 rewrite to odd?
;trying disabled
(defthmd bitn-0-rewrite-to-even
  (implies (integerp x)
           (equal (equal (bitn x 0) 0)
                  (integerp (* 1/2 x)))))

;we probably want this enabled in lib/ but not in support/
(defthmd bits-n-n-rewrite
  (equal (bits x n n)
         (bitn x n)))

(theory-invariant (incompatible (:rewrite bits-n-n-rewrite)
                                (:definition bitn)
                                )
                  :key bitn-and-bits-n-n-can-loop)

(defthm bitn-0-1
  (or (equal (bitn x n) 0)
      (equal (bitn x n) 1))
  :rule-classes nil)


;my strategy with the rules below is to prefer (not (equal (bitn x n) 0)) over (equal (bitn x n) 1)
;this allows subsumption to ...
;but maybe this is a bad idea!
;BOZO if we have f-w chaining rule to handle this issue, perhaps drop these rules?

;bad to have both?
(defthm bitn-not-0-means-1
  (equal (not (equal (bitn x n) 0))
         (equal (bitn x n) 1)))

(defthm bitn-not-1-means-0
  (equal (not (equal (bitn x n) 1))
         (equal (bitn x n) 0)))

;these are bad rules?
(in-theory (disable bitn-not-1-means-0 bitn-not-0-means-1))

(defthm bitn-bitn
  (equal (bitn (bitn x n) 0)
         (bitn x n)))

(defthm bitn-known-not-0-replace-with-1
  (implies (not (equal (bitn x n) 0)) ; backchain-limit?
           (equal (bitn x n)
                  1))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  )

;needed?
(defthm bitn->-0
  (equal (< 0 (bitn x n))
         (not (equal 0 (bitn x n)))))

(defthm bitn-<-1
  (equal (< (BITN X n) 1)
         (equal (BITN X n) 0)))

;useful if bitn-upper-bound and bitn-upper-bound-2 are disabled
(defthm bitn-not->-1
  (implies (and (syntaxp (quotep k))
                (<= 1 k))
           (equal (< k (bitn x n))
                  nil)))

;useful if bitn-upper-bound and bitn-upper-bound-2 are disabled
(defthm bitn-<=-1
  (implies (and (syntaxp (quotep k))
                (< 1 k))
           (equal (< (bitn x n) k)
                  t)))

(defthmd bitn-rec-0
  (implies (integerp x)
           (equal (bitn x 0)
                  (mod x 2))))

;rename?
;is there a bits analog of this theorem?
;BOZO change formal k to n
(defthmd bitn-rec-pos
  (implies (< 0 k) ;k cannot be 0 or negative
           (equal (bitn x k)
                  (bitn (fl (/ x 2)) (1- k))))
  :rule-classes ((:definition :controller-alist ((bitn t t)))))

;BOZO change k param to n
(defthmd bitn-def
  (implies (case-split (integerp k))
           (equal (bitn x k)
                  (mod (fl (/ x (expt 2 k)))
                       2))))

;make bit-not, bit-and, etc. ?
;BOZO or remove this function?
(defun not-eric (x)
  (if (equal x 0)
      1
    0))

(defthm bitn-drop-crucial-bit-and-flip-result
  (implies (and (case-split (rationalp x))
                (case-split (integerp n)) ;drop?
                )
           (and (equal (bitn (+ (expt 2 n) x) n)
                       (not-eric (bitn x n)))
                (equal (bitn (+ x (expt 2 n)) n)
                       (not-eric (bitn x n))))))

;BOZO this looped!
(defthmd bitn-drop-crucial-bit-and-flip-result-alt-gen
  (implies (and (syntaxp (and (quotep j)
                              (< (cadr j) (expt 2 (+ 1 (cadr n)))) ;bitn-sum-lowbits does most of the work
                              (>= (cadr j) (expt 2 (cadr n)))))
                (rationalp j)
                (rationalp x)
                (integerp n)
                )
           (equal (bitn (+ j x) n)
                  (not-eric (bitn (+ (- j (expt 2 n)) x) n)))))

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
                  (not-eric (bitn (+ (+ j (expt 2 n)) x) n)))))

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
                  (<= 0 x))))

;drop silly hyps like: (<= -128 (bitn x 24))
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

;there are many other ways to say that something is even (include those?)
(defthm bitn-even-means-0
  (equal (integerp (* 1/2 (bitn x n)))
         (equal (bitn x n) 0)))

;new - export disabled?
(defthm bitn-too-small
  (implies (and (< x (expt 2 n))
                (<= 0 x) ;case-split?
                )
           (equal (bitn x n)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil))))

;not sure how to handle this.
(defthmd bitn-normal-form
  (equal (equal (bitn x n) 1)
         (not (equal (bitn x n) 0))))

(defthm bitn-bvecp
  (implies (and (<= 1 k)
                (case-split (integerp k)))
           (bvecp (bitn x n) k)))

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

;BOZO change params
(defthm bitn-0
  (equal (bitn 0 k)
         0))

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

;may cause case splits (maybe that's good?)
(defthm bitn-expt-gen
  (implies (case-split (integerp i))
           (equal (bitn (expt 2 i) n)
                  (if (equal i n)
                      1
                    0))))

;BOZO consider having only the rule above?
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

(defthmd bitn-expt-0
  (implies (and (not (equal i n))
		(case-split (integerp i)))
	   (equal (bitn (expt 2 i) n) 0)))

(defthm bitn-0-1
    (or (equal (bitn x n) 0)
        (equal (bitn x n) 1))
  :rule-classes ())

;BOZO enable?
(defthmd bitn-shift-eric
  (implies (and (integerp n)
                (integerp k)
                )
           (equal (bitn (* x (expt 2 k)) n)
                  (bitn x (+ n (- k))))))

(defthmd bitn-shift-eric-2
  (implies (and (integerp n)
                (integerp k)
                )
           (equal (bitn (* (expt 2 k) x) n)
                  (bitn x (+ n (- k))))))

;BOZO replace with bitn-shift-eric ??
(defthmd bitn-shift
  (implies (and (integerp n)
                (integerp k)
                )
           (equal (bitn (* x (expt 2 k)) (+ n k))  ;BOZO rewrite the (+ n k) to match better
                  (bitn x n))))

;dammit, ACL2 unifies 0 with (* 2 x), so this rule can loop!
(defthm bitn-shift-by-2
  (implies (and (syntaxp (not (quotep x)))
                (acl2-numberp n))
           (equal (BITN (* 2 x) n)
                  (bitn x (+ -1 n)))))

(defthmd bitn-plus-mult
  (implies (and (< n m)
                (integerp m)
                (integerp k)
                )
           (equal (bitn (+ x (* k (expt 2 m))) n)
                  (bitn x n))))

;we almost always want to leave this disabled!
(defthmd bitn-plus-bits
  (implies (and (<= m n)
                (integerp m)
                (integerp n)
                )
           (= (bits x n m)
              (+ (* (bitn x n) (expt 2 (- n m)))
                 (bits x (1- n) m)))))

;BOZO it's in r-c nil.  we almost always want to leave this disabled!
(defthm bits-plus-bitn
    (implies (and (<= m n)
                  (integerp m)
		  (integerp n)
		  )
	     (= (bits x n m)
		(+ (bitn x m)
		   (* 2 (bits x n (1+ m))))))
  :rule-classes ())

;drop?
(defthm bits-0-bitn-0
  (implies (and (<= 0 n)
                (integerp n)
                )
           (iff (= (bits x n 0) 0)
                (and (= (bitn x n) 0)
                     (= (bits x (1- n) 0) 0))))
  :rule-classes ())

;Follows from bits-shift-down
(defthmd bitn-shift-2
  (implies (and (<= 0 k)
                (integerp k)
                (integerp r)
                )
           (equal (bitn (fl (/ x (expt 2 r))) k)
                  (bitn x (+ k r)))))

(defthm bitn-shift-by-constant-power-of-2
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (case-split (integerp n))
                )
           (equal (bitn (* k x) n)
                  (bitn x (- n (expo k))))))



;generalize to bits-mod?
(defthmd bitn-mod
  (implies (and (< k n)
                (integerp n)
                (integerp k)
                )
           (equal (bitn (mod x (expt 2 n)) k)
                  (bitn x k))))

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
  :rule-classes ())

;bozo. combine these next 2?

;bozo. dup?
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
                  (bitn x n))))


;this is the most interesting case. perhaps add the other cases for k<0 and k>i-j
(defthm bitn-bits
  (implies (and (<= k (- i j))
                (case-split (<= 0 k))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                )
           (equal (bitn (bits x i j) k)
                  (bitn x (+ j k)))))

(defthmd bitn-shift-3
  (implies (and (bvecp x m)
                (<= m n)
                (integerp k)
                (case-split (integerp n))
                (case-split (integerp m))
                )
           (equal (bitn (+ x (* k (expt 2 m))) n)
                  (bitn k (- n m)))))

;reconcile param names with bits version?
;like  bitn-shift-3
;rename!

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
                  (bitn k (- n m)))))

(defthm bit-expo-c
    (implies (and (<= (- (expt 2 n) (expt 2 k)) x)
                  (< x (expt 2 n))
                  (< k n)
                  (rationalp x);(integerp x) ;gen more!
		  (integerp n)
		  (integerp k)
		  )
	     (equal (bitn x k) 1))
  :rule-classes ())

;Follows from bit-expo-c
;requires x to be an integer, unlike bit-expo-c.
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

;could combine these next two?

;BOZO enable?
(defthmd bvecp-bitn-0
  (implies (bvecp x n)
           (equal (bitn x n) 0)))

;make an alt version?
;trying disabled..
(defthmd bitn-bvecp-0
  (implies (and (bvecp x n)
                (<= 0 m)
                )
           (equal (bitn x (+ m n)) 0)))

;k is a free var
;do we need this, if we have bvecp-longer?
(defthm bitn-bvecp-0-eric
  (implies (and (bvecp x k)
                (<= k n))
           (equal (bitn x n) 0))
  :rule-classes ((:rewrite :match-free :all)))

;sort of a "bitn-tail" like bits-tail?
(defthm bitn-bvecp-1
  (implies (bvecp x 1)
           (equal (bitn x 0) x)))

;rename
(defthmd bvecp-bitn-1
    (implies (and (bvecp x (1+ n))
		  (<= (expt 2 n) x)
                  (natp n))
	     (equal (bitn x n) 1)))

;handle the case where we don't go down to 0?
(defthm bits-bitn
  (implies (and (case-split (integerp i))
                (case-split (<= 0 i))
                )
  (equal (bits (bitn x n) i 0)
         (bitn x n))))
