(in-package "ACL2")

(local (include-book "../support/guards"))

;; Necessary defuns

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

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(local (include-book "../support/lnot"))

;;New stuff:

;used to be called COMP1
(defund lnot (x n)
  (declare (xargs :guard (and (natp x)
                              (integerp n)
                              (< 0 n))))
  (if (natp n)
      (+ -1 (expt 2 n) (- (bits x (1- n) 0)))
    0))

;note that this isn't a rewrite rule b/c we believe it will never need to be
;BOZO make it one anyway?
(defthm lnot-nonnegative-integer-type
  (and (integerp (lnot x n))
       (<= 0 (lnot x n)))
  :rule-classes ((:type-prescription :typed-term (lnot x n))))

;lnot-nonnegative-integer-type is strictly better, and we don't need both
(in-theory (disable (:type-prescription lnot)))

(defthm lnot-natp
  (natp (lnot x n)))

(defthm lnot-upper-bound
  (< (lnot x n) (expt 2 n))
  :rule-classes (:rewrite :linear)
  )

;why is bvecp enabled here?

(defthm lnot-bvecp-simple
  (bvecp (lnot x n) n))

(defthm lnot-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lnot x n) k)))

;perhaps conclude with bits of x and drop the bvecp hyp?
(defthm lnot-lnot
  (implies (and (case-split (natp n))
                (case-split (bvecp x n))
                )
           (equal (lnot (lnot x n) n)
                  x)))

;reorient this rule?
(defthmd lnot-times-2
   (implies (and (case-split (natp x))
                 (case-split (natp n))
                 )
            (equal (+ 1 (* 2 (lnot x n)))
                   (lnot (* 2 x) (1+ n)))))

(defthm lnot-with-n-0
  (equal (lnot x 0)
         0))

;gen?
;make a by-2 version?
;change param name?
;make a better rewrite rule
;RHS isn't simplified!
(defthmd lnot-fl
  (implies (and (<= k n)
                ;(bvecp x n)
                (<= 0 k)
                (integerp n)
                (integerp k)
                )
           (equal (fl (* (/ (expt 2 k)) (lnot x n)))
                  (lnot (fl (/ x (expt 2 k))) (- n k)))))

;gen
;add case-splits
(defthm mod-lnot
  (implies (and (<= n m)
;                (integerp x)
                (integerp n)
                (<= 0 n) ;gen
                (integerp m)
                )
           (equal (mod (lnot x m) (expt 2 n))
                  (lnot (mod x (expt 2 n)) n))))

(defthm mod-lnot-by-2
  (implies (and (< 0 n)
                (integerp x) ;gen?
                (integerp n)
                )
           (equal (mod (lnot x n) 2)
                  (lnot (mod x 2) 1))))

;disable?
(defthm lnot-ignores-bits
  (equal (lnot (bits x (+ -1 n) 0) n)
         (lnot x n)))

(defthmd lnot-ignores-bits-2
  (implies (and (integerp i)
                (<= (+ -1 n) i))
           (equal (lnot (bits x i 0) n)
                  (lnot x n))))

;gen?
;formal m should be n
(defthm bits-lnot
  (implies (and (< i m)
                (case-split (natp j))
                (case-split (integerp m))
                (case-split (integerp i))
                )
           (equal (bits (lnot x m) i j)
                  (lnot (bits x i j) (1+ (- i j))))))

;gen?
(defthm bitn-lnot
  (implies (and (case-split (natp m))
                (case-split (natp n))
                )
           (equal (bitn (lnot x m) n)
                  (if (< n m)
                      (lnot (bitn x n) 1)
                    0))))

;do we still need this, given bitn-lnot?
(defthm bitn-lnot-not-equal
  (implies (and (< k n)
                (integerp n)
                (<= 0 n)
                (integerp k)
                (<= 0 k)
                )
           (not (= (bitn (lnot x n) k)
                   (bitn x k))))
  :rule-classes ())

;could generalize these a lot (when lnot equals a constant, take the lnot of both sides)
;drop bvecp hyp by wrapping bits around conclusion?
(defthm lnot-bvecp-equal-0
  (implies (case-split (bvecp x 1))
           (equal (equal (lnot x 1) 0)
                  (not (equal x 0)))))

(defthm lnot-bvecp-equal-1
  (implies (case-split (bvecp x 1))
           (equal (equal (lnot x 1) 1)
                  (equal x 0))))

;consider enabling?
(defthmd lnot-ignores-mod-special
  (equal (lnot (mod x (expt 2 m)) m)
         (lnot x m)))

;consider enabling?
(defthmd lnot-ignores-mod
  (implies (and (<= m n)
                (case-split (integerp n)))
           (equal (lnot (mod x (expt 2 n)) m)
                  (lnot x m))))

;rename to shift-by-2?
;consider enabling?
(defthmd lnot-shift
  (implies (and (syntaxp (not (quotep x))) ;prevents loops
                (case-split (integerp x))
                (case-split (< 0 n))
                (case-split (integerp n))
                )
           (equal (lnot (* 2 x) n)
                  (+ 1 (* 2 (lnot x (+ -1 n)))))))

;disable?
;BOZO rename the other lnot-fl.  this one should be called lnot-fl.
(defthm lnot-fl-eric
  (equal (lnot (fl x) n)
         (lnot x n)))

(defthm lnot-with-n-not-an-integer
  (implies (not (integerp n))
           (equal (lnot x n)
                  0)))

(defthm lnot-with-n-not-positive
  (implies (<= n 0)
           (equal (lnot x n)
                  0)))
