(in-package "ACL2")

#|

  final-theorem.lisp
  ~~~~~~~~~~~~~~~~~~

We prove the final theorem about qsort here. After all that I had to do, this
should go like a breeze, except (maybe) for the hiccup when (length x) is equal
to 0. But this is not a big deal.

We mark the final theorem by a capital DEFTHM for easy look-up.

|#

(include-book "sort-qs-properties")

(local
(include-book "load-extract")
)

(local
(in-theory (disable alloc-qs load-qs))
)

(local
(in-theory (enable in-situ-equal-intermediate
                   intermediate-in-situ-qsort-equal-qsort))
)

(local
(defthm arith-001
  (implies (and (not (natp (1- l)))
                (natp l))
           (equal l 0))
  :rule-classes :forward-chaining)
)

(local
(defthm len-0-implies-not-consp
  (implies (equal (len x) 0)
           (not (consp x)))
  :hints (("Goal"
           :in-theory (enable len)))
  :rule-classes :forward-chaining)
)

(DEFTHM qsort-is-correct
  (implies (true-listp x)
           (equal (qsort x)
                  (isort x)))
  :hints (("Goal"
           :in-theory (disable natp-posp--1) ; needed for v2-8
           :cases ((not (natp (1- (len x))))))))

;; Finally, we add an mbe version of sort which is isort in the logic and is
;; qsort in under-the-hood execution.  This work is new, i.e., not included
;; in the 2002 ACL2 workshop supporting materials.

(defun sort-list (x)
  (declare (xargs :guard (true-listp x)))
  (mbe :logic (isort x) :exec (qsort x)))

(defthm sort-list-is-correct
  (and (ordp (sort-list x))
       (perm (sort-list x) x)))

;; We now prove that sort-list is idempotent by proving the property about
;; isort.

(defthm <<=-implies-equal
  (implies (and (<<= x y) (not (<< x y)))
           (equal x y))
  :rule-classes :forward-chaining)

(defthm ordp-isort
  (ordp (isort x)))

(in-theory (enable isort insert))

(in-theory (disable qsort-fn-equivalent-isort))

(defthm true-listp-isort
  (true-listp (isort x)))

(defthm insert-equals-cons
  (implies (and (ordp x) (<<= e (car x)) (true-listp x))
           (equal (insert e x) (cons e x))))

(defthm isort-idempotent-1
  (implies (and (ordp x) (true-listp x))
           (equal (isort x) x)))

(defthm isort-idempotent
  (equal (isort (isort x)) (isort x)))

(defthm sort-list-idempotent
  (equal (sort-list (sort-list x)) (sort-list x)))
