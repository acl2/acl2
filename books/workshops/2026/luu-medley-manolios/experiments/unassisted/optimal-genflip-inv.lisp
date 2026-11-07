; optimal-genflip-inv.lisp -- Appendix B, part 4a (end): a pair (gs, hs)
; obtained from (I, I) by flips, i.e. with T2(gs,hs) = T2(I,I), is an
; invertible change of basis in the sense of genflip-basis.lisp.

(in-package "ACL2")

(include-book "optimal-genflip-elim")

;; Entries of sum_j e_j (x) e_j.
(defthm dot-coords-of-id-rows-from
  (implies (and (natp N) (natp i) (<= i N) (natp k) (natp q) (< k N) (< q N))
           (equal (dot-coords k q (id-rows-from N i) (id-rows-from N i))
                  (if (and (<= i k) (equal k q)) 1 0)))
  :hints (("Goal" :induct (ind-up N i))
          ("Subgoal *1/2" :expand ((id-rows-from N i)))))

(defthm bv-listp-of-id-rows-from
  (implies (natp N) (bv-listp N (id-rows-from N i)))
  :hints (("Goal" :induct (ind-up N i))))

(defthm len-of-id-rows-from
  (implies (and (natp N) (natp i) (<= i N))
           (equal (len (id-rows-from N i)) (- N i)))
  :hints (("Goal" :induct (ind-up N i))))

(defthm entry-of-T2-identity
  (implies (and (natp N) (natp k) (natp q) (< k N) (< q N))
           (equal (nth (+ (* k N) q) (T2 N N (identity-rows N) (identity-rows N)))
                  (if (equal k q) 1 0)))
  :hints (("Goal" :in-theory (disable nth-of-T2 dot-coords-of-id-rows-from)
                  :use ((:instance nth-of-T2 (L N) (Us (identity-rows N)) (Vs (identity-rows N)) (p k))
                        (:instance dot-coords-of-id-rows-from (i 0))))))

;; Entries of the identity rows.
(defthm entry-of-identity-rows
  (implies (and (natp N) (natp k) (natp q) (< k N) (< q N))
           (equal (nth q (nth k (identity-rows N))) (if (equal k q) 1 0)))
  :hints (("Goal" :in-theory (disable nth-of-id-rows-from)
                  :use ((:instance nth-of-id-rows-from (i 0))))))

;; Row-wise extensionality for lists of N rows of length N.
(defun rows-diff (M1 M2)
  (declare (xargs :guard t))
  (cond ((atom M1) 0)
        ((atom M2) 0)
        ((equal (car M1) (car M2)) (1+ (rows-diff (cdr M1) (cdr M2))))
        (t 0)))

(defthm natp-of-rows-diff (natp (rows-diff M1 M2)) :rule-classes :type-prescription)

(defthm rows-diff-witness
  (implies (and (true-listp M1) (true-listp M2) (equal (len M1) (len M2))
                (not (equal M1 M2)))
           (and (< (rows-diff M1 M2) (len M1))
                (not (equal (nth (rows-diff M1 M2) M1) (nth (rows-diff M1 M2) M2))))))

(defthm bv-listp-nth-local
  (implies (and (natp N) (bv-listp N M) (natp k) (< k (len M)))
           (and (bvp (nth k M)) (equal (len (nth k M)) N)))
  :hints (("Goal" :induct (ind-xk M k) :in-theory (disable bv-listp-member))))

(defthm T2-eq-identity-implies-rows-sum2-identity
  (implies (and (natp N) (bv-listp N gs) (bv-listp N hs) (equal (len gs) N) (equal (len hs) N)
                (equal (T2 N N gs hs) (T2 N N (identity-rows N) (identity-rows N))))
           (equal (rows-sum2 N N gs hs) (identity-rows N)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (disable entry-of-rows-sum2 entry-of-identity-rows entry-of-T2-identity
                                      rows-diff-witness bv-diff-index-witness bv-listp-member
                                      bv-listp-nth-local)
                  :use ((:instance rows-diff-witness (M1 (rows-sum2 N N gs hs)) (M2 (identity-rows N)))
                        (:instance bv-listp-of-rows-sum2 (NB N) (NC N))
                        (:instance bv-listp-nth-local (M (rows-sum2 N N gs hs))
                                   (k (rows-diff (rows-sum2 N N gs hs) (identity-rows N))))
                        (:instance bv-listp-nth-local (M (identity-rows N))
                                   (k (rows-diff (rows-sum2 N N gs hs) (identity-rows N))))
                        (:instance bv-extensionality
                                   (x (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                           (rows-sum2 N N gs hs)))
                                   (y (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                           (identity-rows N))))
                        (:instance bv-diff-index-witness
                                   (x (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                           (rows-sum2 N N gs hs)))
                                   (y (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                           (identity-rows N))))
                        (:instance entry-of-rows-sum2
                                   (k (rows-diff (rows-sum2 N N gs hs) (identity-rows N)))
                                   (q (bv-diff-index
                                       (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                            (rows-sum2 N N gs hs))
                                       (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                            (identity-rows N)))))
                        (:instance entry-of-identity-rows
                                   (k (rows-diff (rows-sum2 N N gs hs) (identity-rows N)))
                                   (q (bv-diff-index
                                       (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                            (rows-sum2 N N gs hs))
                                       (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                            (identity-rows N)))))
                        (:instance entry-of-T2-identity
                                   (k (rows-diff (rows-sum2 N N gs hs) (identity-rows N)))
                                   (q (bv-diff-index
                                       (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                            (rows-sum2 N N gs hs))
                                       (nth (rows-diff (rows-sum2 N N gs hs) (identity-rows N))
                                            (identity-rows N)))))))))
