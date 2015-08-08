(in-package "ACL2")

(defthm len-nthcdr-le-len-lst--thm
  (<= (len (nthcdr x lst)) (len lst)))

(defthm nthcdr-of-len-lst--thm
  (implies (and (true-listp lst) (natp xx) (>= xx (len lst)))
           (= (nthcdr xx lst) nil)))

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm nthcdr-cdr--thm
  (implies (and (integerp xx) (>= xx 0) (true-listp lst))
           (= (nthcdr xx (cdr lst)) (nthcdr (1+ xx) lst))))

(defthm cdr-nthcdr--thm
  (implies (and (integerp xx) (>= xx 0) (true-listp lst))
           (= (cdr (nthcdr xx lst)) (nthcdr (1+ xx) lst))))

(defthmd cdr-nthcdr-minus-1--thm
  (implies (and (integerp xx) (> xx 0) (true-listp lst))
           (= (nthcdr xx lst) (cdr (nthcdr (1- xx) lst)) )))

(defthm nthcdr-len-minus-2--thm
  (implies (and (true-listp lst) (> (len lst) 1))
           (= (nthcdr (- (len lst) 2) lst)
              (list (nth (- (len lst) 2) lst)
                    (nth (- (len lst) 1) lst)))))

(defthm nthcdr-member-nth--thm
  (implies (and (true-listp lst) (natp xx) (< xx (len lst)))
           (member-equal (nth xx lst) (nthcdr xx lst))))

(defthm nthcdr-member-nth-1--thm
  (implies (and (true-listp lst) (natp xx)
                (< (1+ xx) (len lst)))
           (member-equal (nth (1+ xx) lst) (nthcdr xx lst))))

(defthm nthcdr-len-minus-1--thm
  (implies (and (consp x) (true-listp x))
           (= (nthcdr (1- (len x)) x)
              (list (nth (1- (len x)) x)))))

(defthm nthcdr-preserves-true-listp--thm
  (implies (and (true-listp lst) (natp x))
           (true-listp (nthcdr x lst))))

(defthm nthcdr-ge-len-nil--thm
  (implies (and (true-listp x) (natp q) (>= q (len x)))
           (= (nthcdr q x) nil)))

(defthm nthcdr-lt-len-not-nil--thm
  (implies (and (true-listp x) (not (endp x)) (natp q) (< q (len x)))
           (not (= (nthcdr q x) nil))))

(defthm len-nthcdr-minus-1-gt-len-nthcdr--thm
  (implies (and (true-listp x) (not (endp x)) (natp q) (> q 0) (< q (len x)))
           (> (len (nthcdr (1- q) x)) (len (nthcdr q x)))))

(defthm nth-ge-len-nil--thm
  (implies (and (true-listp x) (natp q) (>= q (len x)))
           (= (nth q x) nil)))

(defthm nthcdr-update-nth--thm
  (implies (and (true-listp lst) (natp ix) (< ix (len lst))
                (natp iy) (< ix iy))
           (= (nthcdr iy (update-nth ix z lst))
              (nthcdr iy lst))))
