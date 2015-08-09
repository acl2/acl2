(in-package "ACL2")

#|

This book is about LAND, a nice version of LOGAND.  LAND takes an extra size parameter, N, and always returns
a bit vector of length N.

|#

(local (include-book "../support/guards"))

;;Necessary defuns:

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

(local (include-book "../support/land"))

;; New stuff

;We expect n to be a positive integer, and x and y to be bit vectors of length n.
(defund binary-land (x y n)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (< 0 n))))
  (logand (bits x (1- n) 0)
          (bits y (1- n) 0)))

(defun formal-+ (x y)
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

(defmacro land (&rest x)
  (declare (xargs :guard (and (consp x)
                              (consp (cdr x))
                              (consp (cddr x)))))
  (cond ((endp (cdddr x)) ;(land x y n) -- the base case
         `(binary-land ,@x))
        (t
         `(binary-land ,(car x)
                       (land ,@(cdr x))
                       ,(car (last x))))))

;Allows things like (in-theory (disable land)) to refer to binary-land.
(add-macro-alias land binary-land)

(defthm land-nonnegative-integer-type
  (and (integerp (land x y n))
       (<= 0 (land x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription land) is no better than land-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-land)))

;drop this if we plan to keep natp enabled?
(defthm land-natp
  (natp (land x y n)))

;BOZO split into 2 rules?
(defthm land-with-n-not-a-natp
  (implies (not (natp n))
           (equal (land x y n)
                  0)))

(defthmd land-bvecp-simple
  (bvecp (land x y n) n))

(defthm land-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (land x y n) k)))


;;
;; Rules to normalize land terms (recall that LAND is a macro for BINARY-LAND):
;;

;This guarantees that the n parameters to nested LAND calls match.
;Note the MIN in the conclusion.
;BOZO do we expect MIN to be enabled?  Maybe we should use IF instead for this and other rules?
(defthm land-nest-tighten
  (implies (and (syntaxp (not (equal m n)))
                (case-split (integerp m))
                (case-split (integerp n))
                )
           (equal (land x (land y z m) n)
                  (land x (land y z (min m n)) (min m n)))))

; allow the n's to differ on this?
(defthm land-associative
  (equal (land (land x y n) z n)
         (land x (land y z n) n)))

(defthm land-commutative
  (equal (land y x n)
         (land x y n)))

; allow the n's to differ on this?
(defthm land-commutative-2
  (equal (land y (land x z n) n)
         (land x (land y z n) n)))

; allow the n's to differ on this?
(defthm land-combine-constants
  (implies (syntaxp (and (quotep x)
                         (quotep y)
                         (quotep n)))
           (equal (land x (land y z n) n)
                  (land (land x y n) z n))))

(defthm land-0
  (equal (land 0 y n)
         0))

;nicer than the analogous rule for logand? is it really?
;BOZO gen the second 1 in the lhs?
(defthm land-1
  (equal (land 1 y 1)
         (bitn y 0)))

(defthm land-self
  (equal (land x x n)
         (bits x (+ -1 n) 0)))

;perhaps use only the main rule, bits-land?
(defthmd bits-land-1
  (implies (and (< i n)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land x y n) i j)
                  (land (bits x i j)
                        (bits y i j)
                        (+ 1 i (- j))))))

;perhaps use only the main rule, bits-land?
(defthmd bits-land-2
  (implies (and (<= n i)
                (case-split (<= 0 j))
                (case-split (integerp n))
                )
           (equal (bits (land x y n) i j)
                  (land (bits x i j)
                        (bits y i j)
                        (+ n (- j))))))

;Notice the call to MIN in the conclusion.
(defthm bits-land
  (implies (and (case-split (<= 0 j))
                (case-split (integerp n))
                (case-split (integerp i))
                )
           (equal (bits (land x y n) i j)
                  (land (bits x i j)
                        (bits y i j)
                        (+ (min n (+ 1 i)) (- j))))))

(defthmd bitn-land-1
  (implies (and (< m n)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land x y n) m)
                  (land (bitn x m)
                        (bitn y m)
                        1))))
(defthmd bitn-land-2
  (implies (and (<= n m)
                (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land x y n) m)
                  0)))

;notice the IF in the conclusion
;we expect this to cause case splits only rarely, since m and n will usually be constants
(defthm bitn-land
  (implies (and (case-split (<= 0 m))
                (case-split (integerp n))
                )
           (equal (bitn (land x y n) m)
                  (if (< m n)
                      (land (bitn x m)
                            (bitn y m)
                            1)
                    0))))

;BOZO see land-equal-0
;drop bvecp hyps and put bitn in conclusion?
(defthm land-of-single-bits-equal-0
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 0 (land x y 1))
                  (or (equal x 0)
                      (equal y 0)))))

(defthm land-of-single-bits-equal-1
  (implies (and (case-split (bvecp x 1))
                (case-split (bvecp y 1))
                )
           (equal (equal 1 (land x y 1))
                  (and (equal x 1)
                       (equal y 1)))))

(defthm land-ones
  (equal (land (+ -1 (expt 2 n)) x n)
         (bits x (+ -1 n) 0))
  :rule-classes ())

;land-with-all-ones will rewrite (land x n) [note there's only one value being ANDed], because (land x n)
;expands to (BINARY-LAND X (ALL-ONES N) N) - now moot???
;BOZO drop bvecp hyp and move to conclusion?
(defthm land-with-all-ones
  (implies (case-split (bvecp x n))
           (equal (land (all-ones n) x n)
                  x)))

(defthmd land-ones-rewrite
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (equal k (1- (expt 2 n))) ;this computes on constants...
                )
           (equal (land k x n)
                  (bits x (+ -1 n) 0))))

(defthm land-def
  (implies (and (integerp x)
                (integerp y)
                (> n 0)
                (integerp n)
                )
           (equal (land x y n)
                  (+ (* 2 (land (fl (/ x 2)) (fl (/ y 2)) (1- n)))
                     (land (mod x 2) (mod y 2) 1))))
  :rule-classes ())

(defthmd land-mod-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (mod (land x y n) 2)
                  (land (mod x 2) (mod y 2) 1))))

;BOZO RHS isn't simplified...
(defthmd land-fl-2
  (implies (and (natp x)
                (natp y)
                (natp n)
                (> n 0))
           (equal (fl (/ (land x y n) 2))
                  (land (fl (/ x 2)) (fl (/ y 2)) (1- n)))))

;BOZO rename to land-with-n-0
;what if n is negative? or not an integer?
(defthm land-x-y-0
  (equal (land x y 0) 0))

;actually, maybe only either x or y must be a bvecp of length n
;n is a free var
(defthm land-reduce
    (implies (and (bvecp x n)
		  (bvecp y n)
		  (natp n)
		  (natp m)
		  (< n m))
	     (equal (land x y m)
                    (land x y n))))

;deceptive name; this only works for single bits!
(defthm land-equal-0
  (implies (and (bvecp i 1)
                (bvecp j 1))
           (equal (equal 0 (land i j 1))
                  (or (equal i 0)
                      (equal j 0)))))

;make alt version?
(defthm land-bnd
  (implies (case-split (<= 0 x))
           (<= (land x y n) x))
  :rule-classes (:rewrite :linear))

;enable? make an alt version??
(defthmd land-ignores-bits
  (equal (land (bits x (+ -1 n) 0) y n)
         (land x y n)))

(defthmd land-with-shifted-arg
  (implies (and (integerp x) ;gen?
                (rationalp y)
                (integerp m)
                (integerp n)
                (<= 0 m)
                )
           (equal (land (* (expt 2 m) x) y n)
                  (* (expt 2 m) (land x (bits y (+ -1 n) m) (+ n (- m)))))))

(defthmd land-expt
  (implies (and (natp n)
                (natp k)
                (< k n))
           (equal (land x (expt 2 k) n)
                  (* (expt 2 k) (bitn x k)))))

(defthm land-slice
  (implies (and (< j i) ;drop? or not?
                (<= i n)
                (integerp n)
                (integerp i)
                (integerp j)
                (<= 0 j)
                )
           (equal (land x (- (expt 2 i) (expt 2 j)) n)
                  (* (expt 2 j) (bits x (1- i) j))))
  :rule-classes ())

(defthm land-upper-bound
  (implies (and (integerp n)
                (<= 0 n))
           (< (land x y n) (expt 2 n)))
  :rule-classes (:rewrite :linear))

(defthm land-upper-bound-tight
  (implies (and (integerp n)
                (<= 0 n))
           (<= (land x y n) (+ -1 (expt 2 n)))))

(defthm land-fl-1
  (equal (land (fl x) y n)
         (land x y n)))

(defthm land-fl-2-eric ;BOZO name conflicted...
  (equal (land x (fl y) n)
         (land x y n)))
