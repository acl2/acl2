(in-package "ACL2")

(include-book "../arithmetic/negative-syntaxp")
(include-book "../arithmetic/power2p")
(local (include-book "../support/bits"))
(local (include-book "../support/guards"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;; Necessary defuns:

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
;;Start of new stuff
;;

;In proofs about RTL terms, i and j are almost always constants
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

(defthm bits-nonnegative-integerp-type
  (and (<= 0 (bits x i j))
       (integerp (bits x i j)))
  :rule-classes (:type-prescription))

;this rule is no better than bits-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription bits)))

(defthm bits-natp
  (natp (bits x i j)))

(defthm bits-with-x-0
  (equal (bits 0 i j)
         0))

(defthm bits-with-x-not-rational
  (implies (not (rationalp x))
           (equal (bits x i j)
                  0)))

(defthm bits-with-i-not-an-integer
  (implies (not (integerp i))
           (equal (bits x i j)
                  0)))

(defthm bits-with-j-not-an-integer
  (implies (not (integerp j))
           (equal (bits x i j)
                  0)))

(defthm bits-with-indices-in-the-wrong-order
  (implies (< i j)
           (equal (bits x i j)
                  0)))

(defthm bits-upper-bound
  (< (bits x i j) (expt 2 (+ 1 i (- j))))
  :rule-classes (:rewrite (:linear :trigger-terms ((bits x i j)))))

;tigher bound for the usual case
(defthm bits-upper-bound-tighter
  (implies (case-split (<= j i))
           (<= (bits x i j) (+ -1 (expt 2 (+ i 1 (- j))))))
  :rule-classes (:rewrite (:linear :trigger-terms ((bits x i j)))))

;this might help stupid hyps get rewritten away...
;perhaps require that z be a constant?
(defthm bits-upper-bound-2
  (implies (<= (expt 2 (+ 1 i (- j))) z)
           (< (bits x i j) z)))

;a is a free var
(defthm bits-force
  (implies (and (<= (* a (expt 2 (+ i 1))) x)
                (< x (* (1+ a) (expt 2 (+ i 1))))
                (integerp x)
                (integerp i)
                (integerp a)
                )
           (equal (bits x i 0)
                  (- x (* a (expt 2 (+ i 1))))))
  :rule-classes nil
  )

;BOZO expensive? disable?
(defthm bits-force-with-a-chosen-neg
  (implies (and (< x 0) ;rarely the case?
                (<= (* -1 (expt 2 (+ i 1))) x)
                (integerp x)
                (integerp i)
                )
           (equal (bits x i 0)
                  (- x (* -1 (expt 2 (+ i 1)))))))

;eventually, I'd like to add a bind-free rule to handle the bits-shift case?
(defthm bits-shift
  (implies (and (case-split (integerp n))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (and (equal (bits (* (expt 2 n) x) i j)
                       (bits x (- i n) (- j n)))
                (equal (bits (* x (expt 2 n)) i j)
                       (bits x (- i n) (- j n))))))

(defthm bits-shift-second-with-more
  (implies (and (case-split (integerp n))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits (* x (expt 2 n) y) i j)
                  (bits (* x y) (- i n) (- j n)))))

(defthm bits-shift-by-constant-power-of-2
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits (* k x) i j)
                  (bits x (- i (expo k)) (- j (expo k))))))

;allows you to split bit vectors into two parts
;free var n (where to split)
;BOZO get rid of the other in favor of this one?
(defthm bits-plus-bits2
  (implies (and ;(rationalp x)
                (integerp i)
                (integerp j)
                (integerp n)
                (<= j n)
                (<= n i))
           (equal (bits x i j)
                  (+ (* (bits x i n) (expt 2 (- n j)))
                     (bits x (1- n) j))))
  :rule-classes nil)

(defthm bits-plus-bits
  (implies (and (integerp m)
                (integerp p)
                (integerp n)
                (<= m p)
                (<= p n))
           (= (bits x n m)
              (+ (bits x (1- p) m)
                 (* (expt 2 (- p m)) (bits x n p)))))
  :rule-classes ())

;this really has two separate cases
;generalize with j not 0?
;this rule often seems helpful, but I'm not sure exactly why
(defthm bits-split-around-zero
  (implies (and (>= x (- (expt 2 (+ i 1))))
                (< x (expt 2 (+ i 1)))
                (integerp x)
                (case-split (integerp i))
                (case-split (<= 0 i))
                )
           (equal (bits x i 0)
                  (if (<= 0 x)
                      x
                    (+ x (expt 2 (+ i 1)))))))

;this should fire after bits-bvecp, so we list it first
(defthm bits-bvecp-when-x-is
  (implies (and (bvecp x k)	;gen k to be something less that the k in the rhs?
                (case-split (<= 0 j))
                )
           (bvecp (bits x i j) k)))

(defthm bits-bvecp
  (implies (and (<= (+ 1 i (- j)) k)
                (case-split (integerp k))
                )
           (bvecp (bits x i j) k)))

;BOZO do we want this rule enabled?
;this is sort of odd
(defthm bits-bvecp-fw
  (implies (equal n (- (1+ i) j)) ; note the EQUAL here to help with the fw chaining
           (bvecp (bits x i j) n))
  :rule-classes
  ((:forward-chaining :trigger-terms ((bits x i j)))))

;BOZO make this one a fw-chaining rule instead of the one above?
(defthm bits-bvecp-simple
  (implies (equal k (+ 1 i (* -1 j)))
           (bvecp (bits x i j) k)))

;included in case bits-bvecp has the problem described above...
(defthm bits-bvecp-simple-2
  (bvecp (bits x (+ -1 i) 0) i))



;I have many theorems dealing with the simplification of bits of a sum

;better names: make the dropped term x, the others a,b,c,...
;;; more bits thms like this!

(defthm bits-sum-drop-irrelevant-term-2-of-2
  (implies (integerp (/ y (expt 2 (+ 1 i))))
           (equal (bits (+ x y) i j)
                  (bits x i j))))

(defthm bits-sum-drop-irrelevant-term-1-of-2
  (implies (integerp (/ y (expt 2 (+ 1 i))))
           (equal (bits (+ y x) i j)
                  (bits x i j))))

(defthm bits-sum-drop-irrelevant-term-3-of-3
  (implies (integerp (/ y (expt 2 (+ 1 i))))
           (equal (bits (+ w x y) i j)
                  (bits (+ w x) i j))))

(defthm bits-sum-drop-irrelevant-term-2-of-3
  (implies (integerp (/ y (expt 2 (+ 1 i))))
           (equal (bits (+ w y x) i j)
                  (bits (+ w x) i j))))

;kind of yucky
(defthmd bits-minus
  (implies (and (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (<= j i)) ;drop?
                (case-split (integerp j))
                )
           (equal (bits (* -1 x) i j)
                  (if (integerp (* 1/2 x (/ (expt 2 i))))
                      0
                    (if (integerp (* x (/ (expt 2 j))))
                        (+ (* 2 (expt 2 i) (/ (expt 2 j))) (- (bits x i j)))
                      (+ -1 (* 2 (expt 2 i) (/ (expt 2 j))) (- (bits x i j))))))))

(defthm bits-minus-alt
  (implies (and (syntaxp (negative-syntaxp x))
                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (<= j i))
                (case-split (integerp j))
                )
           (equal (bits x i j)
                  (if (integerp (* 1/2 (- X) (/ (EXPT 2 I))))
                    0
                    (if (INTEGERP (* (- X) (/ (EXPT 2 J))))
                        (+ (* 2 (EXPT 2 I) (/ (EXPT 2 J))) (- (bits (- x) i j)))
                      (+ -1 (* 2 (EXPT 2 I) (/ (EXPT 2 J))) (- (bits (- x) i j))))))))

;drops hyps like this: (<= (BITS x 30 24) 253)
;Recall that <= gets rewritten to < during proofs
(defthm bits-drop-silly-upper-bound
  (implies (and (syntaxp (quotep k))
                (>= k (+ -1 (expt 2 (+ 1 i (- j)))))
                (case-split (<= j i))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< k (bits x i j))
                  nil)))

;rewrite things like (<= 4096 (BITS x 23 12)) to false
;Recall that <= gets rewritten to < during proofs
(defthm bits-drop-silly-lower-bound
  (implies (and (syntaxp (quotep k))
                (> k (+ -1 (expt 2 (+ 1 i (- j)))))
                (case-split (<= j i))
                (case-split (integerp i))
                (case-split (integerp j))
                )
  (equal (< (bits x i j) k)
         t)))

;rewrite (< -64 (BITS <signal> 64 59)) to t
(defthm bits-drop-silly-bound-3
  (implies (and (syntaxp (quotep k))
                (< k 0)
                )
           (equal (< k (bits x i j))
                  t)))

(defthm bits-drop-silly-bound-4
  (implies (and (syntaxp (quotep k))
                (<= k 0)
                )
           (equal (< (bits x i j) k)
                  nil)))

;This is the rule for which I wish I knew the "parity" of the term being rewritten...
(defthm bits-<-1
  (equal (< (bits x i j) 1)
         (equal (bits x i j) 0)))

;put bits-cancel- in the name?
(defthm bits-at-least-zeros
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (- j2 j)))
                (<= j j2)
                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp j2))
                )
           (equal (< (bits x i j)
                     (* k (bits x i j2)))
                  nil)))

(defthm bits-upper-with-subrange
  (implies (and (syntaxp (quotep k))
                (<= j j2)
                (equal k (expt 2 (- j2 j)))
                (case-split (<= j2 i)) ;drop?
                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp j2))
                )
           (< (BITS x i j)
              (BINARY-+ k (BINARY-* k (BITS x i j2))))))

(defthm bits-upper-with-subrange-alt
  (implies (and (syntaxp (quotep k))
                (<= j j2)
                (equal k (expt 2 (- j2 j)))
                (case-split (<= j2 i)) ;drop?
                (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp j2))
                )
           (equal (< (BINARY-+ k (BINARY-* k (BITS x i j2)))
                     (BITS x i j))
                  nil)))

;make another version for k negative? (t-p should handle?)
(defthm bits-equal-impossible-constant
  (implies (and (syntaxp (quotep k)) ;require that i and j be constants too?
                (<= (expt 2 (+ 1 i (- j))) k)
                )
           (not (equal (bits x i j) k))))

;will this fire?
(defthm bits-compare-to-zero
  (implies (and (case-split (rationalp x))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (not (< 0 (bits x i j)))
                  (equal 0 (bits x i j)))))

;expensive?
;have we done enough to prevent loops?
;should we make a version where we require j to be a constant and then disable this version?
(defthm bits-ignore-negative-bits-of-integer
   (implies (and (syntaxp (not (and (quotep j) (equal 0 (cadr j))))) ;prevents loops
                 (<= j 0)
                 (integerp x)
                 (case-split (integerp j))
                 )
            (equal (bits x i j)
                   (* (expt 2 (- j)) (bits x i 0)))))

;disable since it can be bad to leave "naked" signals and we never want to see expt
(defthmd bits-does-nothing-2
  (implies (and (<= j 0) ;a bit strange (j will usually be zero?)
                (bvecp x (+ i 1)) ;expand?
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits x i j)
                  (* (expt 2 (- j)) x))))

;has the right pattern to rewrite stuff like this: (<= (EXPT 2 J) (BITS Y (+ -1 J) 0)) to nil
(defthm bits-upper-bound-special
  (< (bits x (+ -1 i) 0) (expt 2 i)))

;like bits-reduce
;was called bits-tail
;BOZO choose a name for this...
(defthmd bits-does-nothing
  (implies (and (bvecp x (1+ i))
                (case-split (integerp i))
                )
           (equal (bits x i 0)
                  x)))

(defthm bits-with-bad-index-2
  (implies (not (integerp i))
           (equal (bits x (+ -1 i) 0)
                  0)))

;BOZO rename to begin with "bits-"
(defthmd bvecp-bits-0
   (implies (bvecp x j)
            (equal (bits x i j) 0)))

;to handle mod- correctly
;make an alt version?
(defthm bits-drop-from-minus
  (implies (and (<= y x)
		(bvecp x n)
		(bvecp y n)
		)
	   (equal (bits (+ x (* -1 y)) (+ -1 n) 0)
		  (+ x (* -1 y))
		  )))

;backchain-limit?
(defthm bits-tail
   (implies (and (bvecp x (1+ i))
                 (case-split (acl2-numberp i)))
            (equal (bits x i 0)
                   x)))

(defthm bits-tail-special
   (implies (bvecp x i)
            (equal (bits x (+ -1 i) 0)
                   x)))

(defthmd bits-alt-def
  (equal (bits x i j)
         (if (or (not (integerp i))
                 (not (integerp j)))
             0
           (mod (fl (/ x (expt 2 j))) (expt 2 (+ 1 i (- j)))))))

(defthmd bits-plus-mult-2
   (implies (and (< n k)
                 (integerp y)
                 (integerp k)
                 )
            (equal (bits (+ x (* y (expt 2 k))) n m)
                   (bits x n m))))



;can we replace 0 with any non-negative j?
(defthm bits-less-than-x
  (implies (<= 0 x)
	   (<= (bits x i 0) x))
  :rule-classes (:rewrite :linear))

;should say <= instead of less-than
(defthm bits-less-than-x-gen
  (implies (and (<= 0 x) ;case-split?
                (case-split (<= 0 j))
                (case-split (not (complex-rationalp x)))
                )
	   (<= (bits x i j) x))
  :rule-classes (:rewrite :linear))


(defthmd bits-bits-1
  (implies (and (<= k (- i j))
                (case-split (<= 0 l))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp l))
                )
           (equal (bits (bits x i j) k l)
                  (bits x (+ k j) (+ l j)))))

(defthmd bits-bits-2
  (implies (and (> k (- i j))
                (case-split (<= 0 l))
;                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp l))
                )
           (equal (bits (bits x i j) k l)
                  (bits x i (+ l j)))))

(defthm bits-bits
  (implies (and (case-split (<= 0 l))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                (case-split (integerp l))
                )
           (equal (bits (bits x i j) k l)
                  (if (<= k (- i j))
                      (bits x (+ k j) (+ l j))
                    (bits x i (+ l j))))))

(defthm bits-reduce
  (implies (and (< x (expt 2 (+ 1 i)))
                (case-split (integerp x))
                (case-split (<= 0 x))
                (case-split (integerp i))
                )
           (equal (bits x i 0)
                  x)))

(defthm bits-0
  (equal (bits 0 i j)
         0))



;could prove a version where we drop bits from both args?
(defthm bits-sum-drop-bits-around-arg-2
  (implies (and (<= i i+)
                (integerp y)
                (case-split (integerp i+))
                )
           (equal (bits (+ x (bits y i+ 0)) i j)
                  (bits (+ x y) i j))))

;Follows from BITS-SUM-DROP-BITS-AROUND-ARG-2.
(defthm bits-sum-drop-bits-around-arg-1
  (implies (and (<= i i+)
                (integerp x)
                (case-split (integerp i+))
                )
           (equal (bits (+ (bits x i+ 0) y) i j)
                  (bits (+ x y) i j))))

(defthm bits-sum-drop-bits-around-arg-2-special-case
  (implies (integerp y)
           (equal (bits (+ x (bits y i 0)) i j)
                  (bits (+ x y) i j))))

(defthm bits-sum-drop-bits-around-arg-1-special-case
  (implies (integerp x)
           (equal (bits (+ (bits x i 0) y) i j)
                  (bits (+ x y) i j))))

;rename
;Follows from BVECP-SUM-OF-BVECPS.
(defthm bits-sum-1
  (equal (bits (+ (bits x (+ -1 i) 0)
                  (bits y (+ -1 i) 0))
               i ;actually, this could be anything >= i ??
               0)
         (+ (bits x (+ -1 i) 0)
            (bits y (+ -1 i) 0))))


;export!! enable?
;gen?
;BOZO rename!
(defthmd bits-of-non-integer-special
  (implies (case-split (not (integerp i)))
           (equal (bits x (+ -1 i) 0)
                  0)))

(defthm bits-fl
  (implies (<= 0 j)
           (equal (bits (fl x) i j)
                  (bits x i j))))

;just use bits-fl-eric and bits-shift!
;BOZO drop the fl from the lhs, since it'll be rewritten away...
(defthmd bits-shift-down
  (implies (and (<= 0 j)
                (integerp i)
                (integerp j)
                (integerp k)
                )
           (equal (bits (fl (/ x (expt 2 k)))
                        i
                        j)
                  (bits x (+ i k) (+ j k)))))

(defthmd bits-shift-down-eric
  (implies (and (<= 0 j)
                (integerp i)
                (integerp j)
                (integerp k)
                )
           (equal (bits (* x (/ (expt 2 k)))
                        i
                        j)
                  (bits x (+ i k) (+ j k)))))

; like  bits-plus-mult-1 - remove one of them?
(defthmd bits+2**k-2
  (implies (and (< x (expt 2 k))
                (<= 0 x)
                (rationalp x) ;(integerp x)
                (<= k m)
                (integerp y)
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp k))
                )
           (equal (bits (+ x (* y (expt 2 k))) n m)
                  (bits y (- n k) (- m k)))))

(defthm bits+2**k-2-alt
  (implies (and (< x (expt 2 k))
                (<= 0 x)
                (rationalp x) ;(integerp x)
                (<= k m)
                (integerp y)
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp k))
                )
           (equal (bits (+ x (* (expt 2 k) y)) n m)
                  (bits y (- n k) (- m k)))))

(defthmd bits-fl-by-2
  (equal (fl (* 1/2 (bits x i 0)))
         (bits x i 1)))

(defthm mod-bits-by-2
  (implies (and (integerp x)
                (<= 0 i)
                (integerp i)
                )
           (equal (mod (bits x i 0) 2)
                  (mod x 2))))

;basically the same as bits+2**k-2; drop one?
;move
(defthmd bits-plus-mult-1
  (implies (and (bvecp x k) ;actually, x need not be an integer...
                (<= k m)
                (integerp y)
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp k))
                )
           (equal (bits (+ x (* y (expt 2 k))) n m)
                  (bits y (- n k) (- m k)))))

(defthm bits-mod-0
  (implies (and (integerp x)
                (>= x 0)
                (integerp m)
                (>= m 0)
                (integerp n)
                (>= n 0))
           (iff (= (mod x (expt 2 (+ m n 1))) 0)
                (and (= (bits x (+ m n) n) 0)
                     (= (mod x (expt 2 n)) 0))))
  :rule-classes ())

;this is silly? just open up bits!
(defthm mod-bits-equal
  (implies (= (mod x (expt 2 (1+ i))) (mod y (expt 2 (1+ i))))
           (= (bits x i j) (bits y i j)))
  :rule-classes ())


;not needed?  just expand bits?
(defthmd bits-mod
  (implies (and (case-split (integerp x))
                (case-split (integerp i)) ;gen?
;(case-split (<= 0 i))
                )
           (equal (bits x i 0)
                  (mod x (expt 2 (1+ i))))))

;reorder? make rewrite?
(defthm bits-shift-up
  (implies (and (integerp x)
                (integerp k)
                (<= 0 k)
                (integerp i)
                )
           (equal (* (expt 2 k) (bits x i 0))
                  (bits (* (expt 2 k) x) (+ i k) 0)))
  :rule-classes ())

;export!
;more forms of this? (bits (/ (expt 2 k)) i j)
;bits of a constant power of 2??
;bits of a range of ones (i.e., a difference of powers of 2).
;use power2p??
(defthm bits-expt
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k)) ;BOZO gen?
                )
           (equal (bits (expt 2 k) i j)
                  (if (or (< i j)
                          (< k j)
                          (< i k))
                      0
                    (expt 2 (- k j))))))

(defthm bits-expt-constant
  (implies (and (syntaxp (and (quotep k) (power2p (cadr k))))
                (force (power2p k)) ;bozo do the computation only once
                (case-split (integerp k)) ;gen?
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits k i j)
                  (if (or (< i j)
                          (< (expo k) j)
                          (< i (expo k)))
                      0
                    (expt 2 (- (expo k) j))))))


;BOZO add case-splits?
(defthm mod-bits
  (implies (and (<= 0 i)
                (<= 0 j)
                (integerp j)
                (integerp i))
           (equal (mod (bits x i 0) (expt 2 j))
                  (bits x (min i (+ -1 j)) 0))))



;Unlike bits-tail, this allows j to be non-zero.
;Note that the conclusion is (bits x ...), not just x.
;i is a free variable
;watch out for loops with this rule
(defthmd bits-tighten
  (implies (and (bvecp x i)
                (<= i n)
                (case-split (integerp n))
                )
           (equal (bits x n j)
                  (bits x (+ -1 i) j)))
  :rule-classes ((:rewrite :match-free :all)))