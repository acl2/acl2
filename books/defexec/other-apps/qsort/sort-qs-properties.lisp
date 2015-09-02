(in-package "ACL2")

#|

  sort-qs-properties.lisp
  ~~~~~~~~~~~~~~~~~~~~~~~

This is the book we had been building up on. We prove here that sort-qs is the
same as in-situ-qsort-fn.We use all the theorems we have proved previously. The
main theorem here is still not very clean, simply because I needed to apply
rewrite rules somewhat in the opposite direction. However, this will be as
clean as it gets.:-> And I will get mad at ACL2 for not being able to open up
in-situ-qsort-fn at the right time, which caused me to write the ugly rewrite
rule in-situ-qsort-expansion-hint.

|#

(include-book "split-qs-properties")
(include-book "arithmetic/top-with-meta" :dir :system)

(local
(defthm sort-qs-is-identity-below-lo
  (implies (and (natp lo)
                (natp hi)
                (natp i)
                (< i lo))
           (equal (objsi i (sort-qs lo hi qstor))
                  (objsi i qstor))))
)

(local
(defthm sort-qs-is-identity-above-hi
  (implies (and (natp lo)
                (natp hi)
                (natp i)
                (> i hi))
           (equal (objsi i (sort-qs lo hi qstor))
                  (objsi i qstor))))
)

(local
(defthm extract-qs-identity-for-sort-qs-below-lo
  (implies (and (natp lo)
                (natp hi)
                (natp loprime)
                (natp hiprime)
                (<= loprime hiprime)
                (< hiprime lo))
           (equal (extract-qs loprime hiprime
                             (sort-qs lo hi qstor))
                  (extract-qs loprime hiprime qstor))))
)

(local
(defthm extract-qs-identity-for-sort-qs-above-hi
  (implies (and (natp lo)
                (natp hi)
                (natp loprime)
                (natp hiprime)
                (<= lo hi)
                (< hiprime lo))
           (equal (extract-qs lo hi
                              (sort-qs loprime hiprime qstor))
                  (extract-qs lo hi qstor))))
)

(local
(in-theory (disable extract-qs-decrement-hi))
)

(local
(in-theory (disable split-qs))
)

(local
(defthm arith-001
  (implies (and (not (natp (1- mid)))
                (natp mid))
           (equal mid 0))
  :rule-classes :forward-chaining)
)

(local
(defthm arith-002
  (implies (and (> mid lo)
                (natp lo)
                (natp mid))
           (natp (1- mid)))
  :rule-classes :forward-chaining)
)

(local
(defthm arith-002-for-mv-nth-0
  (implies (and (> (mv-nth 0 (split-qs lo hi splitter qs)) lo)
                (natp lo)
                (natp hi))
           (natp (1- (mv-nth 0 (split-qs lo hi splitter qs)))))
  :hints (("Goal"
           :in-theory (disable split-qs)
           :use ((:instance arith-002
                            (mid (mv-nth 0
                                         (split-qs lo hi splitter qs)))))))
  :rule-classes :type-prescription)
)

(local
(defthm in-situ-qsort-expansion-hint
  (equal (in-situ-qsort-fn (extract-qs lo hi qs))
         (if (endp (extract-qs lo hi qs)) nil
           (if (endp (rest (extract-qs lo hi qs)))
               (list (objsi lo qs))
             (let ((merge (merge-func (extract-qs lo hi qs)
                                      (objsi lo qs)))
                   (ndx (walk (extract-qs lo hi qs)
                              (objsi lo qs))))
               (if (zp ndx)
                   (cons (first merge)
                         (in-situ-qsort-fn (rest merge)))
                 (let ((upper (in-situ-qsort-fn (last-n ndx
                                                        merge)))
                       (lower (in-situ-qsort-fn (first-n ndx merge))))

                   (append lower upper))))))))
)

(local
(in-theory (disable in-situ-qsort-fn))
)

(local
(in-theory (disable in-situ-qsort-expansion-hint))
)

(local
(include-book "load-extract")
)

(local
(defthm first-n-initiated
  (implies (and (natp lo)
                (natp hi)
                (natp w)
                (> w 0)
                (<= (+ lo w) hi))
           (equal (extract-qs lo (1- (+ lo w)) qs)
                  (first-n w (extract-qs lo hi qs))))
  :hints (("Goal"
           :in-theory (enable consp-extract-reduction)
           :use ((:instance first-n-extract-qs-reduction
                            (i (1- (+ lo w))))))))
)

(local
(defthm last-n-initiated
  (implies (and (natp lo)
                (natp hi)
                (natp w)
                (> w 0)
                (<= (+ lo w) hi))
           (equal (extract-qs (+ lo w) hi qs)
                  (last-n w (extract-qs lo hi qs))))
  :hints (("Goal"
           :use ((:instance last-n-extract-qs-reduction
                            (i (1- (+ lo w))))))))
)

(local
(in-theory (enable walk-split-qs-equal
                   merge-func-split-qs-equal))
)

(defthm mv-nth-0>lo-implies-walk>0
  (implies (and (> (mv-nth 0 (split-qs lo hi splitter qs))
                   lo)
                (natp lo)
                (natp hi)
                (<= lo hi))
           (> (walk (extract-qs lo hi qs) splitter)
                       0))
  :rule-classes :forward-chaining)

(local
(defthm walk-returns-a-value-between-0-and-hi-lo
  (implies (and (natp lo)
                (natp hi)
                (<= lo hi))
           (and (>= (walk (extract-qs lo hi qs)
                          (objsi lo qs))
                    0)
                (<= (+ lo (walk (extract-qs lo hi qs)
                                (objsi lo qs)))
                      hi)))
  :hints (("Goal"
           :in-theory (disable walk walk-split-qs-equal)
           :use ((:instance walk-split-qs-equal
                            (splitter (objsi lo qs)))
                 split-qs-returns-a-number-<=hi)))
  :rule-classes :linear)
)

(local
(defthm mv-nth-0-1-reduction-1
  (implies (and (> (mv-nth 0 (split-qs lo hi (objsi lo qs) qs))
                   lo)
                (natp lo)
                (natp hi)
                (<= lo hi))
           (equal (extract-qs  lo (1- (+ lo (walk (extract-qs lo hi qs)
                                                  (objsi lo qs))))
                               (mv-nth 1 (split-qs lo hi (objsi lo qs) qs)))
                  (first-n (walk (extract-qs lo hi qs)
                                 (objsi lo qs))
                           (merge-func (extract-qs lo hi qs)
                                       (objsi lo qs))))))
)

(local
(defthm mv-nth-0-1-reduction-2
  (implies (and (> (mv-nth 0 (split-qs lo hi (objsi lo qs) qs))
                   lo)
                (natp lo)
                (natp hi)
                (<= lo hi))
           (equal (extract-qs  (+ lo (walk (extract-qs lo hi qs)
                                           (objsi lo qs)))
                               hi
                               (mv-nth 1 (split-qs lo hi (objsi lo qs) qs)))
                  (last-n (walk (extract-qs lo hi qs)
                                (objsi lo qs))
                          (merge-func (extract-qs lo hi qs)
                                      (objsi lo qs))))))
)

(local
(in-theory (disable first-n-initiated last-n-initiated))
)
(local
(defthm lo<hi-implies-extract-consp
  (implies (and (< lo hi)
                (natp lo)
                (natp hi))
           (consp (extract-qs (1+ lo) hi qs)))
  :hints (("Goal"
           :expand (extract-qs (1+ lo) hi qs))))
)

(local
(defthm lo<=hi-implies-extract-consp
  (implies (and (<= lo hi)
                (natp lo)
                (natp hi))
           (consp (extract-qs lo hi qs)))
  :hints (("Goal"
           :expand (extract-qs lo hi qs))))
)

(local
(defthm extract-qs-sort-qs-cdr-reduction
  (implies (and (natp lo)
                (natp hi)
                (<= lo hi))
           (equal (extract-qs lo hi
                              (sort-qs (1+ lo) hi qs))
                  (cons (objsi lo qs)
                        (extract-qs (1+ lo) hi
                                    (sort-qs (1+ lo) hi qs))))))
)

(local
(defthm car-of-mv-nth-1-is-objsi-lo
  (implies (and (natp lo)
                (natp hi)
                (<= lo hi))
           (equal (objsi lo (mv-nth 1 (split-qs lo hi (objsi lo qs) qs)))
                  (car (merge-func (extract-qs lo hi qs) (objsi lo qs)))))
  :hints (("Goal"
           :use ((:instance consp-extract-reduction
                            (qs (mv-nth 1 (split-qs lo hi (objsi lo qs)
                                                    qs))))))))
)

(local
(defthm cdr-of-mv-nth-1-is-objsi-lo
  (implies (and (natp lo)
                (natp hi)
                (<= lo hi))
           (equal (extract-qs (1+ lo) hi (mv-nth 1 (split-qs lo hi (objsi lo qs) qs)))
                  (cdr (merge-func (extract-qs lo hi qs) (objsi lo qs)))))
  :hints (("Goal"
           :use ((:instance consp-extract-reduction
                            (qs (mv-nth 1 (split-qs lo hi (objsi lo qs) qs))))))))

)


(defthm sort-qs-equal-in-situ-qsort-fn
  (implies (and (natp lo)
                (natp hi)
                (<= lo hi))
           (equal (extract-qs lo hi (sort-qs lo hi qs))
                  (in-situ-qsort-fn (extract-qs lo hi qs))))
  :hints (("Goal"
           :induct (sort-qs lo hi qs))
          ("Subgoal *1/3'''"  ;; RBK:
           :use ((:instance extract-is-append-of-mid
                            (mid1 (1- (mv-nth 0 (split-qs lo hi (objsi lo qs)
                                                          qs))))
                            (mid2 (mv-nth 0 (split-qs lo hi (objsi lo qs) qs)))
                            (qs (sort-qs lo (1- (mv-nth 0 (split-qs lo hi
                                                                    (objsi lo
                                                                           qs)
                                                                    qs)))
                                         (sort-qs (mv-nth 0 (split-qs lo hi
                                                                      (objsi lo
                                                                             qs)
                                                                      qs))
                                                  hi
                                                  (mv-nth 1 (split-qs lo hi
                                                                      (objsi lo
                                                                             qs)
                                                                      qs))))))))
          ("Subgoal *1/3'6'"  ;; RBK:
           :in-theory (enable in-situ-qsort-expansion-hint))
          ("Subgoal *1/2.1"
           :use in-situ-qsort-expansion-hint)
          ("Subgoal *1/1"
           :in-theory (enable in-situ-qsort-fn)))
  :rule-classes nil)

(defthm sort-qs=in-situ-qsort-fn-final
  (implies (natp lo)
           (equal (extract-qs lo hi (sort-qs lo hi qs))
                  (in-situ-qsort-fn (extract-qs lo hi qs))))
  :hints (("Goal"
           :do-not-induct t
           :cases ((and (natp hi) (<= lo hi))))
          ("Subgoal 1"
           :use sort-qs-equal-in-situ-qsort-fn)))


