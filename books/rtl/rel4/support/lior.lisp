(in-package "ACL2")

#|

This book is about LIOR, a nice version of LOGIOR.  LIOR takes an extra size parameter, N, and always returns
a bit vector of length N.

Todo:
add versions like logand-expt-2 and logand-expt-4 <-- huh?
prove (elsewhere) lemmas mixing lior with other functions
|#

;; Necessary defuns:

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

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund all-ones (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (if (zp n)
      0 ;degenerate case
    (1- (expt 2 n))))

(local (include-book "lior-proofs"))

;; Start of new stuff:

(defund binary-lior (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))
                  :verify-guards nil))
  (logior (bits x (1- n) 0)
          (bits y (1- n) 0)))

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defmacro lior (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(lior x y n) -- the base case
         `(binary-lior ,@x))
        (t
         `(binary-lior ,(car x)
                       (lior ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable lior)) to refer to binary-lior.
(add-macro-alias lior binary-lior)

(defthm lior-nonnegative-integer-type
  (and (integerp (lior x y n))
       (<= 0 (lior x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription lior) is no better than lior-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lior)))

;drop this if we plan to keep natp enabled?
(defthm lior-natp
  (natp (lior x y n)))

(defthm lior-with-n-not-a-natp
  (implies (not (natp n))
           (equal (lior x y n)
                  0)))

(defthmd lior-bvecp-simple
  (bvecp (lior x y n) n))

(defthm lior-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lior x y n) k)))


;;
;; Rules to normalize lior terms (recall that LIOR is a macro for BINARY-LIOR):
;;

;; allow sizes to differ on these?

(defthm lior-associative
  (equal (lior (lior x y n) z n)
         (lior x (lior y z n) n)))

(defthm lior-commutative
  (equal (lior y x n)
         (lior x y n)))

(defthm lior-commutative-2
  (equal (lior y (lior x z n) n)
         (lior x (lior y z n) n)))

(defthm lior-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (lior x (lior y z n) n)
                  (lior (lior x y n) z n))))

(defthm lior-0
  (implies (case-split (bvecp y n))
           (equal (lior 0 y n)
                  y)))

;nicer than the analogous rule for logior?
(defthm lior-1
  (implies (case-split (bvecp y 1))
           (equal (lior 1 y 1)
                  1)))

(defthm lior-self
  (implies (and (case-split (bvecp x n))
                (case-split (integerp n)))
           (equal (lior x x n)
                  x)))

(defthmd bits-lior-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lior x y n) i j)
                  (lior (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j))))))

(defthmd bits-lior-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (lior x y n) i j)
                  (lior (bits x i j)
                        (bits y i j)
                        (+ n (- j))))))

;notice the call to MIN in the conclusion
(defthm bits-lior
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (lior x y n) i j)
                  (lior (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j))))))

(defthmd bitn-lior-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lior x y n) m)
                  (lior (bitn x m)
                        (bitn y m)
                        1))))

(defthmd bitn-lior-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lior x y n) m)
                  0)))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-lior
  (implies (and (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (lior x y n) m)
                  (if (< m n)
                      (lior (bitn x m)
                            (bitn y m)
                            1)
                    0))))

;or could wrap bits around conclusion?
(defthm lior-equal-0
  (implies (and (case-split (bvecp x n))
                (case-split (bvecp y n))
                (case-split (integerp n))
                )
           (equal (equal 0 (lior x y n))
                  (and (equal x 0)
                       (equal y 0)))))

(defthm lior-of-single-bits-equal-0
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 0 (lior x y 1))
                  (and (equal x 0)
                       (equal y 0)))))

(defthm lior-of-single-bits-equal-1
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 1 (lior x y 1))
                  (or (equal x 1)
                      (equal y 1)))))

(defthm lior-ones
  (implies (and (case-split (bvecp x n))
                (case-split (natp n)) ;gen
                )
           (equal (lior (1- (expt 2 n)) x n)
                  (1- (expt 2 n))))
  :rule-classes ())

;lior-with-all-ones will rewrite (lior x n) [note there's only one value being ANDed], because (lior x n)
;expands to (BINARY-LIOR X (ALL-ONES N) N) - now moot???
(defthm lior-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (lior (all-ones n) x n)
                  (all-ones n))))

(defthm lior-ones-rewrite
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)
                              (equal (cadr k) (1- (expt 2 (cadr n))))))
                (force (equal k (1- (expt 2 n))))
		(case-split (natp n))
                (case-split (bvecp x n)))
           (equal (lior k x n)
                  (1- (expt 2 n)))))

(defthm lior-def
    (implies (and (integerp x)
		  (integerp y)
		  (< 0 n)
		  (integerp n))
	     (equal (lior x y n)
		    (+ (* 2 (lior (fl (/ x 2)) (fl (/ y 2)) (1- n)))
		       (lior (mod x 2) (mod y 2) 1))))
  :rule-classes ())

(defthm lior-mod-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (mod (lior x y n) 2)
		    (lior (mod x 2) (mod y 2) 1))))

(defthm lior-fl-2
    (implies (and (natp x)
		  (natp y)
		  (natp n)
		  (> n 0))
	     (equal (fl (/ (lior x y n) 2))
		    (lior (fl (/ x 2)) (fl (/ y 2)) (1- n)))))

(in-theory (disable lior-mod-2 lior-fl-2))

;BOZO rename
(defthm lior-x-y-0
  (equal (lior x y 0) 0))

(defthm lior-reduce
  (implies (and (bvecp x n)
                (bvecp y n)
                (< n m)
                (natp n) ;gen?
                (natp m)
                )
           (equal (lior x y m) (lior x y n))))

;whoa! this is a *lower* bound !
;make alt version?
(defthm lior-bnd
  (implies (case-split (bvecp x n))
           (<= x (lior x y n)))
  :rule-classes (:rewrite :linear))

;get rid of the bvecp hyps (do that for many lemmas like this one)
;BOZO rename to lior-with-shifted-arg
(defthm lior-plus
    (implies (and (bvecp y m)
		  (bvecp x (- n m))
                  (<= m n)
		  (natp m)
                  (integerp n)
                  )
	     (= (lior (* (expt 2 m) x) y n)
		(+ (* (expt 2 m) x) y)))
  :rule-classes ())

(defthm lior-shift
    (implies (and (bvecp x (- n m))
		  (bvecp y (- n m))
                  (integerp n) ;(not (zp n))
		  (natp m)
		  (<= m n)
                  )
	     (= (lior (* (expt 2 m) x)
		      (* (expt 2 m) y)
		      n)
		(* (expt 2 m) (lior x y (- n m)))))
  :rule-classes ())

(defthm lior-expt
    (implies (and (natp n)
		  (natp k)
		  (< k n)
		  (bvecp x n))
	     (= (lior x (expt 2 k) n)
		(+ x (* (expt 2 k) (- 1 (bitn x k))))))
  :rule-classes ())

;interesting.  not the same as lior-bvecp (here, m can be smaller than n)
;rename !!
(defthm lior-bvecp-2
  (implies (and (bvecp x m)
                (bvecp y m)
                )
           (bvecp (lior x y n) m)))

(defthm lior-upper-bound
  (< (lior x y n) (expt 2 n))
  :rule-classes (:rewrite :linear))

(defthm lior-upper-bound-tight
  (implies (<= 0 n)
           (<= (lior x y n) (1- (expt 2 n))))
  :rule-classes (:rewrite :linear))

(defthm lior-fl-1
  (equal (lior (fl x) y n)
         (lior x y n)))

(defthm lior-fl-2-eric
  (equal (lior x (fl y) n)
         (lior x y n)))

(local (include-book "bits"))
