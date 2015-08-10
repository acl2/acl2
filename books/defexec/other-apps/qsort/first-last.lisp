(in-package "ACL2")

#|

  first-last.lisp
  ~~~~~~~~~~~~~~~

In this book, we define the functions first-n and last-n, and prove theorems
about them. This is important because if we look at the sort-qs function
closely we will notice that the recursive calls are to a list which is first-n
of the original splitted list,marked by an index produced by split-qs. Hence
the functions first-n and last-n have a big role to play. We actually will make
the connection explicit in another intermediate function we will define later,
which will be called intermediate-in-situ-qsort.

|#

(include-book "programs")

(local
(defthm arith-001
  (implies (natp i)
           (equal (+ -1 1 i) i)))
)

(defun first-n (i x)
  (if (zp i) nil
    (cons (first x) (first-n (1- i) (rest x)))))

(defun last-n (i x)
  (if (zp i) x
    (last-n (1- i) (rest x))))

(defthm first-last-cons-reduction
  (implies (natp i)
           (equal (first-n (1+ i)
                           (cons e x))
                  (cons e (first-n i x)))))

(defthm first-n-last-n-append-reduction
  (implies (<= i (len x))
           (equal (append (first-n i x)
                          (last-n i x))
                  x)))

(defthm first-len-reduction
  (equal (len (first-n i x))
         (nfix i)))


(defthm append-first-reduction-len
  (implies (and (equal z (append x y))
                (equal n (len x))
                (true-listp x))
           (equal (first-n n z)
                  x)))

(defthm append-last-reduction-len
  (implies (and (equal z (append x y))
                (equal n (len x)))
           (equal (last-n n z)
                  y)))

(defthm append-first-reduction
  (equal (first-n i (append (first-n i x) y))
         (first-n i x)))

(in-theory (enable len))

(defthm first-n-length-is-x
  (implies (and (true-listp x)
		(equal i (len x)))
	   (equal (first-n i x) x)))

(defthm last-n-true-listp-reduction
  (implies (true-listp x)
           (true-listp (last-n i x))))

(in-theory (disable len))


