(in-package "ACL2")

#|

 load-extract.lisp
 ~~~~~~~~~~~~~~~~~

In this book we prove the algebra between load-qs, alloc-qs, and extract-qs. In
particular, we prove that if some list is loaded into the array, and then the
same list is extracted out, then what we are left is the array. This will
immediately mean that qsort is correct, given that sort-qs is
correct. Basically, the rules in this book push the extract-qs function inside
load and alloc and ultimately transforms it into the first-n function. Thus
after the boom certifies the "only" thing required to be proved is the
correctness of sort-qs.

As an addition, we also prove some theorems on extract-qs itself. Those
theorems logically should have been in the file extraction.lisp. But we have it
here, simply because many of them require ideas about extract-n, a function we
define locally here. Reasoning about extract-qs often gets complicated, and we
reason about extract-n there.

|#

(include-book "programs")
(include-book "first-last")

(set-verify-guards-eagerness 0)

(local
(defun extract-n (lo n qstor)
  (declare (xargs :stobjs (qstor)))
    (if (zp n) nil
    (cons (objsi lo qstor)
          (extract-n (1+ lo) (1- n) qstor))))
)

(local
(defthm extract-n-update-reduction
  (implies (and (natp i) (natp lo) (< i lo))
	   (equal (extract-n lo N (update-objsi i e qstor))
		  (extract-n lo N qstor))))
)

;; I need to prove objsi and update-objsi rules for each of the
;; functions involved, to make sure that I work in the right place of
;; the array.

(local
(defthm objsi-load-reduction
  (implies (and (natp i)
		(natp lo)
		(< i lo))
	   (equal (objsi i (load-qs x lo N qs))
		  (objsi i qs))))
)

(local
(defthm load-extract-n-reduction
  (implies (and (natp lo)
		(force (natp N)))
	   (equal (extract-N lo N (load-qs x lo N qs))
		  (first-n n x))))
)


(in-theory (disable alloc-qs load-qs))

(local
(defthm first-n-extract-n-reduction
  (implies (and (natp lo)
                (natp N)
                (natp i)
                (<= i N))
           (equal (extract-n lo i qs)
                  (first-n i (extract-n lo n qs))))
  :rule-classes nil)
)

(local
(defthm extract-qs-n-reduction
  (implies (and (equal n (1+ (- hi lo)))
                (natp hi)
                (natp lo)
                (<= lo hi))
           (equal (extract-qs lo hi qs)
                  (extract-n lo n qs)))
  :hints (("Goal"
           :induct (extract-n lo n qs)))
  :rule-classes nil)
)

(local
(in-theory (disable extract-n))
)

(local
(in-theory (disable first-n extract-qs))
)

(local
(defthm arith-001
  (implies (and (<= lo hi)
                (natp lo)
                (natp hi))
           (natp (1+ (- hi lo))))
  :hints (("Goal"
           :in-theory (enable natp)))
  :rule-classes :forward-chaining)
)

(defthm load-alloc-extract-qs-same
  (implies (and (equal n (1+ (- hi lo)))
                (natp lo)
                (natp hi)
                (<= lo hi))
           (equal (extract-qs lo hi
                              (load-qs x lo n qs))
                  (first-n n x)))
  :hints (("Goal"
           :use ((:instance extract-qs-n-reduction
                            (qs (load-qs x lo n qs)))))))

(local
(defthm arith-002
  (implies (and (< lo i)
                (natp lo)
                (natp i))
           (natp (- i lo)))
  :hints (("Goal"
           :in-theory (enable natp)))
  :rule-classes :forward-chaining)
)

(defthm first-n-extract-qs-reduction
  (implies (and (natp lo)
                (natp hi)
                (natp i)
                (< lo i)
                (<= i hi))
           (equal (extract-qs lo i qs)
                  (first-n (1+ (- i lo))
                           (extract-qs lo hi qs))))
  :hints (("Goal"
           :use ((:instance extract-qs-n-reduction
                            (n (1+ (- hi lo))))
                 (:instance first-n-extract-n-reduction
                            (n (1+ (- hi lo)))
                            (i (1+ (- i lo))))
                 (:instance extract-qs-n-reduction
                            (n (1+ (- i lo)))
                            (hi i))
                 (:instance arith-001))))
  :rule-classes nil)

(local
(include-book "extraction")
)

(local
(in-theory (disable extract-qs-decrement-hi))
)


(defthm last-n-extract-qs-reduction
  (implies (and (natp lo)
                (natp hi)
                (natp i)
                (< lo i)
                (<= i hi))
           (equal (extract-qs (1+ i) hi qs)
                  (last-n (1+ (- i lo))
                          (extract-qs lo hi qs))))
  :hints (("Goal"
           :use ((:instance extract-is-append-of-mid
                            (mid1 i)
                            (mid2 (1+ i))))))
  :rule-classes nil)

