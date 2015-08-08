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

(defun bits (x i j)
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

(local (include-book "bits"))
(local (include-book "bitn"))
;(local (include-book "../arithmetic/top"))
(local (include-book "../arithmetic/expt"))
(local (include-book "../arithmetic/mod"))
(local (include-book "../arithmetic/mod"))
(local (include-book "../arithmetic/arith"))
(local (include-book "../arithmetic/arith2"))
(local (include-book "../arithmetic/integerp"))
(local (include-book "bvecp"))

(local (in-theory (enable expt-minus)))

#|
(defun LNOT (x n)
  (1- (- (expt 2 n) x)))
|#

;used to be called COMP1
(defund lnot (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
    0))

;note that this isn't a rewrite rule b/c we believe it will never need to be
(defthm lnot-nonnegative-integer-type
  (and (integerp (lnot x n))
       (<= 0 (lnot x n)))
  :hints (("Goal" :in-theory (enable lnot)))
  :rule-classes ((:type-prescription :typed-term (lnot x n))))

;lnot-nonnegative-integer-type is strictly better, and we don't need both
(in-theory (disable (:type-prescription lnot)))

(defthm lnot-natp
  (natp (lnot x n)))

(defthm lnot-upper-bound
  (< (lnot x n) (expt 2 n))
  :hints (("Goal" :in-theory (enable lnot)))
  :rule-classes (:rewrite :linear)
  )

;why is bvecp enabled here?

(defthm lnot-bvecp-simple
  (bvecp (lnot x n) n)
  :hints (("Goal" :in-theory (enable bvecp lnot))))

(defthm lnot-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lnot x n) k))
  :hints (("Goal" :in-theory (disable lnot-bvecp-simple)
           :use lnot-bvecp-simple)))

(defthm lnot-lnot
  (implies (and (case-split (natp n))
                (case-split (bvecp x n))
                )
           (equal (lnot (lnot x n) n)
                  x))
  :hints (("Goal" :in-theory (enable lnot bvecp bits-does-nothing))))

;reorient this rule?
(defthmd lnot-times-2
   (implies (and (case-split (natp x))
                 (case-split (natp n))
                 )
            (equal (+ 1 (* 2 (lnot x n)))
                   (lnot (* 2 x) (1+ n))))
   :hints (("Goal" :in-theory (enable lnot expt-split)
            :use (:instance bits-shift (n 1) (i n) (j 0)))))

(defthm lnot-with-n-0
  (equal (lnot x 0)
         0)
  :hints (("Goal" :in-theory (enable lnot)))
  )


(encapsulate
 ()

 (local
  (defthm fl-lnot-1
    (implies (and (integerp n) (>= n k)
                  (integerp k)
                  (>= k 0) ;drop? and propagate..
                  (integerp x) (>= x 0)
                  (< x (expt 2 n))
                  )
             (equal (/ (lnot x n) (expt 2 k))
                    (+ (expt 2 (- n k))
                       (/ (- -1 x) (expt 2 k)))))
    :rule-classes ()
    :hints (("Goal" :in-theory (set-difference-theories
                                (enable lnot expt-split)
                                '( ;a10
                                   ))
             ))))

;this looks fragile
 (local (defthm fl=
          (implies (equal x y)
                   (equal (fl x) (fl y)))
          :rule-classes ()))

 (local (defthm fl-lnot-2
          (implies (and (integerp n) (>= n k)
                        (integerp k) (>= k 0)
                        (integerp x) (>= x 0) (< x (expt 2 n)))
                   (equal (fl (/ (lnot x n) (expt 2 k)))
                          (fl (+ (expt 2 (- n k))
                                 (/ (- -1 x) (expt 2 k))))))
          :rule-classes ()
          :hints (("Goal" :in-theory (disable ;a10
                                      )
                   :use ((:instance fl-lnot-1)
                         (:instance fl=
                                    (x (/ (lnot x n) (expt 2 k)))
                                    (y (+ (expt 2 (- n k))
                                          (/ (- -1 x) (expt 2 k))))))))))

 (local (include-book "../arithmetic/fl"))

 (local (defthm fl-lnot-3
          (implies (and (integerp n) (>= n k)
                        (integerp k) (>= k 0)
                        (integerp x) (>= x 0) (< x (expt 2 n)))
                   (equal (fl (/ (lnot x n) (expt 2 k)))
                          (+ (expt 2 (- n k))
                             (fl (/ (- -1 x) (expt 2 k))))))
          :rule-classes ()
          :hints (("Goal" :in-theory (enable lnot)
                   :use ((:instance fl-lnot-2)
                         )))))

;gen?
;make a by-2 version?
;change param name?
;make a better rewrite rule
 (defthmd lnot-fl-aux
   (implies (and (<= k n)
                 (bvecp x n)
                 (<= 0 k)
                 (integerp n)
                 (integerp k)
                 )
            (equal (fl (* (/ (expt 2 k)) (lnot x n)))
                   (lnot (fl (/ x (expt 2 k))) (- n k))))
   :hints (("Goal" :in-theory (set-difference-theories
                               (enable lnot bvecp)
                               '(bits-fl ;a10
                                 ;fl-minus-gen
                                 ))
            :use ((:instance fl-lnot-3)
                  (:instance fl-m+1 (m x) (n (expt 2 k)))
                  ))))

 )

;disable?
(defthm lnot-ignores-bits
  (equal (lnot (bits x (1- n) 0) n)
         (lnot x n))
  :hints (("Goal" :in-theory (enable lnot))))

(defthmd lnot-ignores-bits-2
  (implies (and (integerp i)
                (<= (1- n) i))
           (equal (lnot (bits x i 0) n)
                  (lnot x n)))
  :hints (("Goal" :in-theory (enable lnot))))

;disable?
(defthm lnot-fl-eric
  (equal (lnot (fl x) n)
         (lnot x n))
  :hints (("Goal" :in-theory (enable lnot))))

;is this okay? dropped the fl...
(local (defthmd lnot-fl-eric-helper
   (implies (and (<= k n)
                 ;(bvecp x n)
                 (<= 0 k)
                 (integerp n)
                 (integerp k)
                 )
            (equal (fl (* (/ (expt 2 k)) (lnot x n)))
                   (lnot (/ (bits x (1- n) 0) (expt 2 k)) (- n k))))
   :hints (("Goal" :in-theory (disable lnot-fl-aux)
            :use ((:instance lnot-fl-aux (x (bits x (1- n) 0 ))))))
   ))


;BOZO move!
(DEFTHM BITS-SHIFT-inv
  (IMPLIES (AND (CASE-SPLIT (INTEGERP N))
                (CASE-SPLIT (INTEGERP I))
                (CASE-SPLIT (INTEGERP J)))
           (EQUAL (BITS (* (/ (EXPT 2 N)) X) I J)
                  (BITS X (+ I N) (+ J N))))
  :hints (("Goal" :in-theory (disable bits-shift)
           :use (:instance bits-shift (n (- n))))))


;why did I have to open up bits??
;perhaps export this?
(local (defthmd lnot-fl-eric-helper-2
   (implies (and (<= k n)
                 (<= 0 k)
                 (integerp n)
                 (integerp k)
                 )
            (equal (lnot (/ (bits x (1- n) 0) (expt 2 k)) (- n k))
                   (lnot (/ x (expt 2 k)) (- n k))))
   :hints (("Goal" :in-theory (e/d ( lnot) (
                                            LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE)) ;BOZO
            :use ((:instance bits-shift (n (- k)) (i (+ -1 N (* -1 K))) (j 0))

                  )))))

;lacks the bvecp hyp
(defthmd lnot-fl
   (implies (and (<= k n)
                 (<= 0 k)
                 (integerp n)
                 (integerp k)
                 )
            (equal (fl (* (/ (expt 2 k)) (lnot x n)))
                   (lnot (fl (/ x (expt 2 k))) (- n k))))
   :hints (("Goal" :use  lnot-fl-eric-helper-2
            :in-theory (enable  lnot-fl-eric-helper  lnot-fl-eric-helper-2))))





(encapsulate
 ()

 (local
  (defthm mod-lnot-1
    (implies (and (integerp x)
                  (>= x 0)
                  (integerp n)
                  (>= n 0) ;BOZO try dropping
                  (integerp m)
                  (>= m n)
                  (< x (expt 2 m))
                  (< x (expt 2 n)) ;new
                  )
             (equal (lnot x m)
                    (+ (lnot x n) (* (expt 2 n) (1- (expt 2 (- m n)))))))
    :rule-classes ()
    :hints (("goal"  :in-theory (enable lnot expt-split)
             ))))


 (local
  (defthm mod-lnot-2-thm
    (implies (and (integerp x)
                  (>= x 0)
                  (integerp n)
                  (>= n 0)
                  (integerp m)
                  (>= m n)
                  (< x (expt 2 m))
                  (< x (expt 2 n)) ;new
                  )
             (equal (mod (lnot x m) (expt 2 n))
                    (mod (+ (lnot x n) (* (expt 2 n) (1- (expt 2 (- m n))))) (expt 2 n))))
    :rule-classes ()
    :hints (("goal" :use (mod-lnot-1)))))

 (local
  (defthm mod-lnot-3
    (implies (and (integerp x)
                  (>= x 0)
                  (integerp n)
                  (>= n 0)
                  (integerp m)
                  (>= m n)
                  (< x (expt 2 m))
                  )
             (equal (mod (lnot x m) (expt 2 n))
                    (mod (lnot (mod x (expt 2 n)) m) (expt 2 n))))
    :otf-flg t
    :rule-classes ()
    :hints (("goal" :in-theory (enable lnot ; bits
                                       )
             :use ((:instance mod-difference-elim-second (x1 (1- (expt 2 m))) (x2 x) (y (expt 2 n)))
                   (:instance expt-weak-monotone)
;                 (:instance lnot-bnds (n m))
;                              (:instance mod+-thm (m (lnot x n)) (n (expt 2 n)) (a (1- (expt 2 (- m n)))))

                   )))))

 (local
  (defthm mod-lnot-4
    (implies (and (integerp x)
                  (>= x 0)
                  (integerp n)
                  (>= n 0)
                  (integerp m)
                  (>= m n)
                  (< x (expt 2 n))
                  )
             (equal (mod (lnot x m) (expt 2 n))
                    (mod (lnot x n) (expt 2 n))))
    :rule-classes ()
    :hints (("goal"
             :use (mod-lnot-2-thm
                   (:instance expt-weak-monotone)
;			(:instance lnot-bnds (n m))
                   (:instance mod-mult-eric (x (lnot x n)) (y (expt 2 n)) (a (1- (expt 2 (- m n)))))
                   )))))

 (local
  (defthm mod-lnot-5
    (implies (and (integerp x)
                  (>= x 0)
                  (integerp n)
                  (>= n 0)
                  (integerp m)
                  (>= m n)
                  (< x (expt 2 m)))
             (equal (mod (lnot x m) (expt 2 n))
                    (mod (lnot (mod x (expt 2 n)) n) (expt 2 n))))
    :rule-classes ()
    :hints (("goal" :use (mod-lnot-3
                          (:instance mod-lnot-4 (x (mod x (expt 2 n))))
;                                     (:instance mod-bnd-1 (m x) (n (expt 2 n)))
;                                     (:instance mod>=0 (m x) (n (expt 2 n)))
                          )))))

;gen
;add case-splits
;write in terms of bvecp?
 (defthm mod-lnot-aux
   (implies (and (< x (expt 2 m)) ;drop!
                 (<= n m)
                 (integerp x)
                 (<= 0 x)
                 (integerp n)
                 (<= 0 n) ;gen
                 (integerp m)
                 )
            (equal (mod (lnot x m) (expt 2 n))
                   (lnot (mod x (expt 2 n)) n)))
   :hints (("goal" :in-theory (enable lnot)
            :use (mod-lnot-5
;(:instance mod-equal (m (lnot (mod x (expt 2 n)) n)) (n (expt 2 n)))
;(:instance mod-bnd-1 (m x) (n (expt 2 n)))
;                  (:instance mod>=0 (m x) (n (expt 2 n)))
                  ))))
 )




(local (include-book "../arithmetic/top"))


;BOZO move this!
(defthm bits-ignores-mod-special
  (equal (bits (mod x (expt 2 m)) (1- m) 0)
         (bits x (1- m) 0)
         )
  :hints (("goal" :in-theory (enable bits)))
  )

;BOZO move this!
(defthm bits-ignores-mod
  (implies (and (<= m n)
                (case-split (integerp n))
                ;(integerp m)
                )
           (equal (bits (mod x (expt 2 n)) (1- m) 0)
                  (bits x (1- m) 0)
                  ))
  :hints (("goal" :in-theory (enable bits)))
  )

(defthm lnot-ignores-mod-special
  (equal (lnot (mod x (expt 2 m)) m)
         (lnot x m))
  :hints (("Goal" :in-theory (enable lnot)))
  )

(defthm lnot-ignores-mod
  (implies (and (<= m n)
                (case-split (integerp n)))
           (equal (lnot (mod x (expt 2 n)) m)
                  (lnot x m)))
  :hints (("Goal" :in-theory (enable lnot)))
  )

;consider enabling?
(defthmd mod-lnot-aux2
   (implies (and (<= n m)
                 (integerp x) ;will be dropped below
                 (integerp n)
                 (<= 0 n) ;gen
                 (integerp m)
                 )
            (equal (mod (lnot x m) (expt 2 n))
                   (lnot (mod x (expt 2 n)) n))) ;note the lack of m in the conclusion
   :hints (("Goal" :in-theory (disable MOD-LNOT-aux)
            :use (:instance mod-lnot-aux (x (mod x (expt 2 m)))))))

;no (integerp x) hyp
(defthmd mod-lnot
   (implies (and (<= n m) ;handle the other case?
                 (integerp n)
                 (<= 0 n) ;gen
                 (integerp m)
                 )
            (equal (mod (lnot x m) (expt 2 n))
                   (lnot (mod x (expt 2 n)) n))) ;note the lack of m in the conclusion
   :hints (("Goal" :use (:instance mod-lnot-aux2 (x (fl x)))
            :in-theory (disable mod-lnot-aux2 ))))

(defthm mod-lnot-by-2
  (implies (and (< 0 n)
                (integerp x) ;gen?
                (integerp n)
                )
           (equal (mod (lnot x n) 2)
                  (lnot (mod x 2) 1)))
  :hints (("Goal" :in-theory (disable lnot-ignores-mod
                                      LNOT-IGNORES-MOD-SPECIAL
                                      mod-lnot)
           :use ((:instance lnot-ignores-mod (n 1) (m n))
                 (:instance mod-lnot (m n) (n 1))))))

(local (defthmd bits-lnot-aux
  (implies (and (< i m)
                (case-split (bvecp x m)) ;dropped below..
                (case-split (integerp m))
                (case-split (integerp i))
                (case-split (natp j)) ;gen?
                )
           (equal (bits (lnot x m) i j)
                  (lnot (bits x i j) (1+ (- i j)))))
  :hints (("Goal" :cases ((>= i j))
           :in-theory (e/d (bits bvecp lnot-fl) ( LNOT-IGNORES-MOD  MOD-LNOT  LNOT-IGNORES-MOD-SPECIAL))))))



;gen?
;BOZO formal m should be n
(defthm bits-lnot
  (implies (and (< i m)
                (case-split (natp j))
                (case-split (integerp m))
                (case-split (integerp i))
                )
           (equal (bits (lnot x m) i j)
                  (lnot (bits x i j) (1+ (- i j)))))
  :hints (("Goal" :use (:instance bits-lnot-aux (x (bits x (1- m) 0)))
           :in-theory (e/d (bvecp) ()))))


#|
(defthm bits-lnot-2
  (implies (and (< i m)
                (case-split (integerp m))
                (case-split (integerp i))
                (case-split (natp j)) ;gen?
                (not (bvecp x m)) ;note!
                (integerp x)
                )
           (equal (bits (lnot x m) i j)
                  (lnot (bits x i j) (1+ (- i j)))))
  :hints (("Goal" :cases ((>= i j))
           :in-theory (enable bvecp lnot))))



|#

;gen?
(defthm bitn-lnot
  (implies (and (case-split (natp m))
                (case-split (natp n))
                ;(case-split (bvecp x m))
                )
           (equal (bitn (lnot x m) n)
                  (if (< n m)
                      (lnot (bitn x n) 1)
                    0)))
  :hints (("Goal" :in-theory (enable bitn BVECP-BITS-0
                                     ))))

;drop?
(defthm bitn-lnot-not-equal
  (implies (and (< k n)
                (integerp n)
                (<= 0 n)
                (integerp k)
                (<= 0 k)
                )
           (not (= (bitn (lnot x n) k)
                   (bitn x k))))
  :hints (("Goal" :in-theory (disable BITN-KNOWN-NOT-0-REPLACE-WITH-1) ;why needed?
; :in-theory (enable bvecp)
           :use (:instance bitn-0-1 (n k))
           ))
  :rule-classes ())

;could generalize these a lot (when lnot equals a constant, take the lnot of both sides)
;drop bvecp hyp by wrapping bits around conclusion?
(defthm lnot-bvecp-equal-0
  (implies (case-split (bvecp x 1))
           (equal (equal (lnot x 1) 0)
                  (not (equal x 0))))
  :hints (("goal" :in-theory (enable lnot bvecp))))

(defthm lnot-bvecp-equal-1
  (implies (case-split (bvecp x 1))
           (equal (equal (lnot x 1) 1)
                  (equal x 0)))
  :hints (("goal" :in-theory (enable lnot bvecp))))

(defthmd lnot-shift
  (implies (and (syntaxp (not (quotep x))) ;prevents loops
                (case-split (integerp x))
                (case-split (< 0 n))
                (case-split (integerp n))
                )
           (equal (lnot (* 2 x) n)
                  (+ 1 (* 2 (lnot x (1- n))))))
  :hints (("Goal" :in-theory (enable lnot))))





#| BOZO get this to work and use in stick-proofs instead of bitn-lnot-not-equal?

;gen!
(defthm lnot-x-not-equal-x
  (implies (and (natp n) (natp x))
           (not (equal (lnot x n) x)))
  :hints (("Goal" :in-theory (enable lnot)))
)

|#


(defthm lnot-with-n-not-an-integer
  (implies (not (integerp n))
           (equal (lnot x n)
                  0))
  :hints (("Goal" :in-theory (enable lnot))))

(defthm lnot-with-n-not-positive
  (implies (<= n 0)
           (equal (lnot x n)
                  0))
  :hints (("Goal" :in-theory (enable lnot))))