(in-package "ACL2")

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(include-book "ground-zero")
(local (include-book "../arithmetic/fl"))
(local (include-book "../arithmetic/expt"))
(local (include-book "../arithmetic/expo"))

;change params on lemmas in this book to match those on ash?

#|(defun ash (i c)
(FLOOR (BINARY-* (IFIX I) (EXPT '2 C))
       '1))
|#

;(thm (rationalp (ash x n))) goes through?

;the (ash 1 x) form shows up in the function decode
(defthm bvecp-ash-1
  (implies (and (case-split (< x n))
                (case-split (integerp n))
                (case-split (integerp x))
                )
           (bvecp (ASH 1 x) n))
  :hints (("Goal" :in-theory (enable ash bvecp floor))))

;is this dumb?
(defthmd ash-rewrite
    (implies (integerp n)
	     (equal (ash n i)
		    (fl (* n (expt 2 i)))))
    :hints (("Goal" :in-theory (enable ash))))

(defthm ash-nonnegative
  (implies (<= 0 i)
           (<= 0 (ash i c)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm ash-nonnegative-type
  (implies (<= 0 i)
           (and (rationalp (ash i c))
                (<= 0 (ash i c))))
  :rule-classes ( :type-prescription)
  :hints (("Goal" :in-theory (enable ash))))

(defthm ash-with-c-non-integer
  (implies (not (integerp c))
           (equal (ash i c)
                  (ifix i)))
  :hints (("Goal" :in-theory (enable ash))))

