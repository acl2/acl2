(in-package "ACL2")

#|
This book includes lemmas about LOGAND.  Note that LOGAND is a macro which expands to nested calls to
BINARY-LOGAND. Both LOGAND and BINARY-LOGAND are built into ACL2.

This book contains only results; all the proofs are done in the book logand-proofs.

Todo:
 use set-invisible-fns-alist - or find a better way?
 rules for logand x with lognot x anywhere in there?
 should logand-with-0 be both sides? what about logand-with-minus-one
 how order rules for efficiency? perhaps make a separate documentation book?
 any other log lemmas?
 are the 4 enough for assoc comm functions?

|#
(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(include-book "ground-zero")
(local (include-book "logand-proofs"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))
;(set-inhibit-warnings) ; restore theory warnings (optional)


;;
;; Rules to normalize logand terms (recall that LOGAND is a macro for BINARY-LOGAND):
;;

(defthm logand-associative
  (equal (logand (logand i j) k)
         (logand i (logand j k))))

(defthm logand-commutative
  (equal (logand j i)
         (logand i j)))

(defthm logand-commutative-2
  (equal (logand j i k)
         (logand i j k)))

(defthm logand-combine-constants
  (implies (syntaxp (and (quotep i)
                         (quotep j)))
           (equal (logand i j k)
                  (logand (logand i j) k))))


;;
;; LOGAND with special values
;;

(defthm logand-with-non-integer-arg
  (implies (or (not (integerp i))
               (not (integerp j)))
           (equal (logand i j)
                  0)))

;0 should always be brought to the front of logand
;should we have a rule with the second arg being 0?
(defthm logand-with-zero
  (equal (logand 0 j) 0))

;-1 should always be brought to the front of logand
;should we have both cases or not?
(defthm logand-with-minus-one
  (implies (case-split (integerp i))
           (equal (logand -1 i) i)))



;;
;; Type facts
;;

;this goes through:
;(thm (integerp (logand i j)))


(defthm logand-integer-type-prescription
  (integerp (logand i j))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logand))))



;These three go together.

;logand is negative iff either arg is negative

;Didn't make this a rewrite rule to avoid backchaining on (integerp (logand i j)) -- should never happen, but
;just in case.
(defthm logand-non-negative-integer-type-prescription
  (implies (or (<= 0 i)
               (<= 0 j))
           (and (<= 0 (logand i j))
                (integerp (logand i j))))
  :rule-classes (:type-prescription))

(defthm logand-negative-integer-type-prescription
  (implies (and (< i 0)
                (< j 0)
                (case-split (integerp i))
                (case-split (integerp j)))
           (and (< (logand i j) 0)
                (integerp (logand i j))))
  :rule-classes (:type-prescription))

; rewrites (<= 0 (logand i j)) and (< (logand i j) 0)
;could this perhaps not fire (say, during backchaining) because of case-splitting of the conclusion, causing
;us to wish we had a simple rule that natp args imply logand is natp?
;maybe don't want this one?
(defthm logand-negative-rewrite
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (< (logand i j) 0)
                  (and (< i 0)
                       (< j 0)))))

(defthm logand-non-negative
  (implies (or (<= 0 x)
               (<= 0 y)
               )
           (<= 0 (logand x y))))

;There's no nice logand-positive rule.  Nor is there a clear rewrite for (< 0 (logand i j))
;For logand to be positive, the arguments must have bits that overlap, and there's no way to state this.
(defthm logand-non-positive-integer-type-prescription
    (implies (and (<= i 0)
                  (<= j 0))
	     (and (<= (logand i j) 0)
		  (integerp (logand i j))))
  :rule-classes (:type-prescription))

(defthm logand-non-positive-rewrite
    (implies (and (<= i 0)
                  (<= j 0))
	     (<= (logand i j) 0)))

#| do we want this?
(defthm logand-negative
  (implies (and (< i 0)
                (< j 0)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (and (integerp (logand i j))
                (< (logand i j) 0)))
  :hints (("Goal" :in-theory (enable logand)))
  :rule-classes (:rewrite (:type-prescription)))
|#



; If logand is less than -1, then both i and j are <= -1, and at least one of them is strictly < -1.
(defthm logand-less-than-minus-one
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< (logand i j) -1)
                  (or (and (<= i -1) (< j -1))
                      (and (<= j -1) (< i -1))))))

;BOZO move!
;perhaps put on a backchain limit?
(defthm integer-tighten-bound
  (implies (integerp x)
           (equal (< -1 x)
                  (<= 0 x))))
#|
;rewrite < -1 to <= 0?
;simplify the conclusion?
(defthm logand-negative-5
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< -1 (logand i j))
                  (not (and (< i 0)
                            (< j 0))))))

:hints (("Goal" :cases ((equal j -1) (equal i -1))
         :in-theory (enable logand))))

|#



(defthm logand-self
  (implies (case-split (integerp i))
           (equal (logand i i) i)))

(defthm logand-equal-minus-one
  (equal (EQUAL (LOGAND i j) -1)
         (and (equal i -1)
              (equal j -1))))

(defthm logand-even
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (INTEGERP (* 1/2 (logand i j)))
                  (or (INTEGERP (* 1/2 i))
                      (INTEGERP (* 1/2 j))))))

;weird?
(defthm logand-0-when-one-arg-is-odd
  (implies (and (not (integerp (* 1/2 j)))
                (case-split (integerp j))
                (case-split (integerp i))
                )
           (and (equal (equal (logand i j) 0)
                       (and (integerp (* 1/2 i))
                            (equal (logand (fl (* 1/2 i)) (fl (* 1/2 j))) 0)))
                (equal (equal (logand j i) 0)
                       (and (integerp (* 1/2 i))
                            (equal (logand (fl (* 1/2 i)) (fl (* 1/2 j))) 0))))))

(defthm logand-simp-1
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (LOGAND (+ 1 (* 2 i))
                          (+ 1 (* 2 j)))
                  (+ 1 (* 2 (logand i j))))))

;add to this
;make linear?
(defthm logand-upper-bound-1
  (implies (<= 0 i)
           (<= (logand i j) i)))


;BOZO same as  logand-upper-bound-1
(defthm logand-bnd
   (implies (<= 0 x)
            (<= (logand x y) x))
   :rule-classes :linear
   )


;trying disabled...
(defthmd logand-with-1
  (implies (case-split (integerp i))
           (equal (logand 1 i)
                  (if (evenp i)
                      0
                    1))))

;trying disabled...
;rename
;BOZO make a nice rule for logand with 1?
(defthmd logand-special-value
  (implies (case-split (integerp j))
           (equal (equal (logand 1 j) j)
                  (or (equal j 0) (equal j 1)))))

(defthmd logand-def
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (logand i j)
              (+ (* 2 (logand (fl (* 1/2 i)) (fl (* 1/2 j))))
                 (logand (mod i 2) (mod j 2)))))
  :rule-classes  ((:definition :controller-alist ((binary-logand t t)))))


(defthm fl-logand-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (fl (* 1/2 (logand i j)))
                  (logand (fl (* 1/2 i)) (fl (* 1/2 j))))))

(defthm floor-logand-by-2
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (floor (logand i j) 2)
                    (logand (floor i 2) (floor j 2)))))

(defthm mod-logand-by-2
  (equal (mod (logand i j) 2)
         (logand (mod i 2) (mod j 2))))

;allow them to occur in other orders (perhaps with intervening terms)?
;think about this
;make a version for logior
(defthm logand-i-lognot-i
  (implies (case-split (integerp i))
           (equal (LOGAND i (LOGNOT i))
                  0)))






;make a nice recognizer?
;handle negative case?
;rename?
(defthmd logand-ones
  (implies (and (< i (expt 2 n)) ;drop and wrap bits around i?
                (<= 0 i)
                (case-split (integerp i))
                )
           (equal (logand i (1- (expt 2 n)))
                  i)))

#|

;change name and param names eventually
(defthm AND-BITS-A
  (implies (and (integerp x); (>= x 0)
                (integerp k); (>= k 0)
                )
           (equal (logand x (expt 2 k))
                  (* (expt 2 k) (bitn x k))))
  :rule-classes ())

|#

(defthm AND-DIST-B
   (implies (and (integerp x) (>= x 0)
                 (integerp y) (>= y 0)
                 (integerp n) (>= n 0))
            (= (logand (* (expt 2 n) x) y)
               (* (expt 2 n) (logand x (fl (/ y (expt 2 n)))))))
   :rule-classes ())


;BOZO also have logand-with-zero
(defthm logand-0
  (equal (logand 0 j) 0))


(defthmd logand-rewrite
  (implies (and (case-split (integerp x))
                (case-split (integerp y))
                )
           (equal (logand x y)
                  (+ (* 2 (logand (fl (/ x 2)) (fl (/ y 2))))
                     (logand (mod x 2) (mod y 2)))))
  :rule-classes ((:definition :controller-alist ((binary-logand t t)))))

(defthm logand-even-2
  (implies (and (integerp i)
                (integerp j))
           (equal (or (= (mod i 2) 0)
                      (= (mod j 2) 0))
                  (= (mod (logand i j) 2) 0)))
  :rule-classes ())