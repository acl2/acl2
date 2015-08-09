(in-package "ACL2")

#|

    programs.lisp
    ~~~~~~~~~~~~~

We consider an example of how to write an in-situ quicksort function in
ACL2. For efficiency, we would like to use a common store which holds the array
we are sorting in place. This leads us to write a quicksort using stobjs. Our
spec is the standard insertion sort, and we would like to prove that the
quicksort produces the same answer as the insertion sort.

The present version has been updated from the original 2002 ACL2 Workshop
supporting materials to incorporate stobjs inlining.

|#

(set-verify-guards-eagerness 1)

(include-book "total-order")
(include-book "nth-update-nth")
(include-book "arithmetic/top-with-meta" :dir :system)

;(defthm natp-compound-recognizer
;  (iff (natp n)
;       (and (integerp n)
;	    (>= n 0)))
;  :rule-classes :compound-recognizer)

(in-theory (disable natp))

(local
(defthm len-resize-list
  (equal (len (resize-list l n d))
         (nfix n))))

;; The store just has one field: objs

(defstobj qstor
  (objs :type (array T (0))
        :initially nil
        :resizable t)
  :inline t)

(local
(defthm objsp-is-true-listp
  (equal (objsp x) (true-listp x))))

(defthm nth-update-nth-diff-objsi
  (implies (not (equal (nfix n) (nfix m)))
           (equal (objsi n (update-objsi m v l)) (objsi n l))))

(defthm nth-update-nth-same-objsi
  (implies (equal (nfix n) (nfix m))
           (equal (objsi n (update-objsi m v l)) v)))

(defthm update-nth-update-nth-same-objsi
  (equal (update-objsi n v (update-objsi n x l))
         (update-objsi n v l)))

(defthm update-nth-update-nth-diff-objsi
  (implies (not (equal (nfix n) (nfix m)))
           (equal (update-objsi n v (update-objsi m x l))
                  (update-objsi m x (update-objsi n v l))))
  :rule-classes ((:rewrite :loop-stopper ((n m)))))

(in-theory (disable objsi update-objsi))

(defun alloc-qs (N qstor)
  (declare (xargs :stobjs qstor))
  (resize-objs N qstor))

(local
(defthm alloc-qs-qstorp
  (implies (qstorp qs)
           (qstorp (alloc-qs N qs)))))

(local
(defthm objs-length-alloc-qs
  (equal (objs-length (alloc-qs N qs))
         (nfix N))))

(local
(defthm objs-length-update-objs
  (equal (len (nth 0 (update-objsi m x l)))
         (len (update-nth m x (nth 0 l))))
  :hints (("Goal" :in-theory (enable update-objsi)))))

(defun load-qs (x lo N qstor)
  (declare (xargs :guard (and (true-listp x)
                              (natp lo)
                              (natp N)
                              (<= (+ N lo)
                                  (objs-length qstor)))
                  :stobjs qstor))
  (if (zp N) qstor
    (let ((qstor (update-objsi lo (first x) qstor)))
      (load-qs (rest x) (1+ lo) (1- N) qstor))))

(local
(defthm load-qs-qstorp
  (implies (qstorp qs)
           (qstorp (load-qs x i N qs)))
  :hints (("Goal" :in-theory (enable update-objsi)))))

(local
(defthm load-qs-objs-length
  (implies (and (natp i)
                (natp N)
                (<= (+ i N) (objs-length qs)))
           (= (objs-length (load-qs x i N qs))
              (objs-length qs)))
  :hints (("Goal" :in-theory (enable update-objsi)))))

(defun extract-qs (lo hi qstor)
  (declare (xargs :guard (and (natp lo)
                              (natp hi)
                              (< hi (objs-length qstor)))
                  :stobjs qstor
                  :measure (nfix (1+ (- hi lo)))))
  (if (and (natp lo)
           (natp hi)
           (<= lo hi))
      (cons (objsi lo qstor)
            (extract-qs (1+ lo) hi qstor))
    nil))

(defun swap (i j qstor)
  (declare (xargs :guard (and (natp i)
                              (natp j)
                              (< i (objs-length qstor))
                              (< j (objs-length qstor)))
                  :stobjs qstor))
  (let* ((temp (objsi i qstor))
	 (qstor (update-objsi i (objsi j qstor) qstor))
	 (qstor (update-objsi j temp qstor)))
    qstor))

(local
(defthm swap-preserves-qstorp
  (implies (qstorp qs)
           (qstorp (swap i j qs)))
  :hints (("Goal" :in-theory (enable update-objsi)))))

(local
(defthm swap-preserves-objs-length
  (implies (and (natp i)
                (natp j)
                (< i (objs-length qs))
                (< j (objs-length qs)))
           (= (objs-length (swap i j qs))
              (objs-length qs)))
  :hints (("Goal" :in-theory (enable update-objsi)))))

(local
(in-theory (disable alloc-qs swap qstorp objs-length)))

(defun ndx< (x y)
  (declare (xargs :guard t))
  (if (and (natp x)
           (natp y))
      (< x y)
    t))

(defun ndx<= (x y)
  (declare (xargs :guard t))
  (if (and (natp x)
           (natp y))
      (<= x y)
    t))

(verify-guards <<)

(defun split-qs (lo hi splitter qstor)
  (declare (xargs :guard (and (integerp lo)
                              (integerp hi)
                              (<= lo (objs-length qstor))
                              (< hi (objs-length qstor)))
                  :stobjs qstor
		  :measure (nfix (1+ (- hi lo)))))
  (if (ndx< hi lo)
      (mv lo qstor)
    (let* ((swap-lo (<<= splitter (objsi lo qstor)))
           (swap-hi (<< (objsi hi qstor) splitter))
           (qstor (if (and swap-lo swap-hi)
                      (swap lo hi qstor)
                    qstor)))
      (split-qs (if (implies swap-lo swap-hi)
                    (1+ lo)
                  lo)
                (if (implies swap-hi swap-lo)
                    (1- hi)
                  hi)
                splitter qstor))))

(local
(defthm qstorp-split-qs
  (implies (qstorp qs)
           (qstorp (cadr (split-qs lo hi x qs))))))

(local
(defthm objs-length-split-qs
  (implies (and (natp lo)
                (natp hi)
                (<= lo (objs-length qs))
                (< hi (objs-length qs)))
           (= (objs-length (cadr (split-qs lo hi x qs)))
              (objs-length qs)))))

;; I do not like to write defthms in the middle of function definitions, but I
;; do it here, simply because the sort-qs function defined soon below is a pain in
;; the butt to go thru....

(local
(in-theory (enable alloc-qs swap qstorp objs-length)))

(defthm property-of-swap
  (implies (and (natp i)
                (natp lo)
                (natp hi))
           (equal (objsi i (swap lo hi qs))
                  (if (equal i lo)
                      (objsi hi qs)
                    (if (equal i hi)
                        (objsi lo qs)
                      (objsi i qs)))))
  :hints (("Subgoal 3"
           :cases ((equal lo hi)))))

(in-theory (disable swap))

(local
(defthm arith-001
  (implies (and (not (natp (1- hi)))
                (natp hi))
           (equal hi 0))
  :rule-classes :forward-chaining)
)

(local
(defthm split-qs-returns-a-value-<=-hi+1
  (implies (and (natp lo)
                (natp hi)
                (<= lo hi))
  (<= (mv-nth 0 (split-qs lo hi splitter qs))
      (1+ hi)))
  :hints (("Goal"
           :induct (split-qs lo hi splitter qs)
           :do-not-induct t)))
)

(defthm split-qs-returns-natp
  (implies (and (natp lo)
                (natp hi))
           (natp (mv-nth 0 (split-qs lo hi splitter qs)))))

(local
(defthm arith-002
  (implies (and (<= i hi)
                (natp i))
           (<= i (1+ hi)))
  :rule-classes :forward-chaining)
)

(local
(defthm arith-004
  (implies (and (<= i hi)
                (natp i)
                (natp hi))
           (not (equal i (1+ hi))))
  :rule-classes :forward-chaining)
)

(local
(defthm if-splitter-is-lo-then-split-qs-neq-hi+1
  (implies (and (natp lo)
                (natp hi)
                (<= lo hi)
                (equal splitter (objsi lo qs)))
           (not (equal (mv-nth 0 (split-qs lo hi splitter qs)) (1+ hi))))
  :hints (("Goal" ; needed for v2-8 addition of natp-posp book
           :in-theory (disable natp-posp--1))
           ("Subgoal *1/5"
           :do-not-induct t
           :in-theory (disable split-qs-returns-a-value-<=-hi+1))
          ("Subgoal *1/5.1"
           :use ((:instance split-qs-returns-a-value-<=-hi+1
                            (hi (1- hi))
                            (splitter (objsi lo qs)))))

          ("Subgoal *1/5.2"
           :use ((:instance split-qs-returns-a-value-<=-hi+1
                             (lo (1+ lo))
                             (hi (1- hi))
                             (qs (swap lo hi qs))
                             (splitter (objsi lo qs)))))))
)

(local
(defthm arith-003
  (implies (and (<= i (1+ hi))
                (natp i)
                (natp hi)
                (not (equal i (1+ hi))))
           (<= i hi))
  :rule-classes nil)
)


(defthm split-qs-returns-a-number-<=hi
  (implies (and (natp lo)
                (natp hi)
                (equal splitter (objsi lo qs))
                (<= lo hi))
           (<= (mv-nth 0 (split-qs lo hi splitter qs))
               hi))
  :hints (("Goal"
           :in-theory (disable split-qs)
           :use ((:instance arith-003
                            (i (mv-nth 0 (split-qs lo hi (objsi lo qs) qs)))))))
  :rule-classes :linear)

(defun sort-qs (lo hi qstor)
  (declare (xargs :guard (and (natp lo)
                              (natp hi)
                              (<= lo (objs-length qstor))
                              (< hi (objs-length qstor)))
                  :verify-guards nil
                  :stobjs qstor
                  :measure (nfix (- hi lo))
                  :hints (("Goal"
                           :in-theory (enable natp)
                           :induct (split-qs lo hi splitter qs)))))
   (if (ndx<= hi lo)
       qstor
     (mv-let (index qstor)
         (split-qs lo hi (objsi lo qstor) qstor)
       (if (ndx<= index lo)
           (sort-qs (1+ lo) hi qstor)
         (let* ((qstor (sort-qs index hi qstor))
                (qstor (sort-qs  lo (1- index) qstor)))
           qstor)))))

(local
(in-theory (disable alloc-qs swap qstorp objs-length)))

(local
(defthm split-qs-<=-objs-length
  (implies (and (integerp lo)
                (integerp hi)
                (< lo (objs-length qs))
                (< hi (objs-length qs)))
           (<= (car (split-qs lo hi x qs))
               (objs-length qs)))
  :rule-classes :linear))

(local
(defthm mv-nth-0-is-car
  (equal (mv-nth 0 x) (car x))
  :hints (("Goal" :in-theory (enable mv-nth)))))

(local
(defthm mv-nth-1-is-cadr
  (equal (mv-nth 1 x) (cadr x))
  :hints (("Goal" :in-theory (enable mv-nth)))))

(local
(defthm qstorp-sort-qs
  (implies (qstorp qs)
           (qstorp (sort-qs lo hi qs)))))

(local
(defthm objs-length-sort-qs
  (implies (and (natp lo)
                (natp hi)
                (<= lo (objs-length qs))
                (< hi (objs-length qs)))
           (= (objs-length (sort-qs lo hi qs))
              (objs-length qs)))))

(verify-guards sort-qs)

(local (in-theory (disable mv-nth-0-is-car mv-nth-1-is-cadr)))

(defun qsort (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x) ()
    (with-local-stobj qstor
      (mv-let (rslt qstor)
          (let* ((size (length x))
                 (qstor (alloc-qs size qstor))
                 (qstor (load-qs x 0 size qstor))
                 (qstor (sort-qs 0 (1- size) qstor)))
            (mv (extract-qs 0 (1- size) qstor)
                qstor))
        rslt))))

;; Now we define the abstract spec.

(defun insert (e x)
  (declare (xargs :guard t))
  (if (or (atom x)
          (<< e (first x)))
      (cons e x)
    (cons (first x)
          (insert e (rest x)))))

(defun isort (x)
  (declare (xargs :guard t))
  (if (atom x) ()
    (insert (first x)
            (isort (rest x)))))



