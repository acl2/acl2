;; implements a merge-sort based sorting of trees

(in-package "ACL2")
(include-book "sort-help")

;; changed to return paired lists (will need to strip-cdrs)
(defun merge-sort-of-ordered-alists (x y taxon-index-alist)
  (declare (xargs :guard (and (good-taxon-index-halist
                               taxon-index-alist)
                              (alistp-gen x)
                              (alistp-gen y)
                              (subset (strip-cars-gen x)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist))
                              (subset (strip-cars-gen y)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))
                  :measure (+ (len x) (len y))))
  (if (atom x)
      y
    (if (atom y)
        x
      (let* ((pair-x (car x))
             (key-x  (car pair-x))
             (pair-y (car y))
             (key-y  (car pair-y)))
        (if (< (cdr (het key-x taxon-index-alist))
               (cdr (het key-y taxon-index-alist)))
            (hons pair-x
                  (merge-sort-of-ordered-alists
                   (cdr x) y taxon-index-alist))
          (hons pair-y
                (merge-sort-of-ordered-alists
                 x (cdr y) taxon-index-alist)))))))

(defun sort-the-alist-by-merge
  (alst taxon-index-alist)
  (declare (xargs :guard (and (good-taxon-index-halist
                               taxon-index-alist)
                              (alistp-gen alst)
                              (subset (strip-cars-gen alst)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))
                  :verify-guards nil))
  (if (atom alst)
      alst
    (if (atom (cdr alst))
        alst
      (let ((evens-list (evens-gen alst))
            (odds-list (odds-gen alst)))
        (merge-sort-of-ordered-alists
          (sort-the-alist-by-merge evens-list taxon-index-alist)
          (sort-the-alist-by-merge odds-list taxon-index-alist)
          taxon-index-alist)))))


(defthm subset-strip-cars-through-merge
  (implies (and (subset (strip-cars-gen x) z)
                (subset (strip-cars-gen y) z))
           (subset (strip-cars-gen
                    (merge-sort-of-ordered-alists
                     x y tia)) z)))

(defthm subset-strip-cars-through-sort
  (implies (subset (strip-cars-gen x) y)
           (subset (strip-cars-gen
                    (sort-the-alist-by-merge x z)) y)))

(defthm alistp-gen-merge-sort-of-ordered
  (implies (and (alistp-gen x)
                (alistp-gen y))
           (alistp-gen (merge-sort-of-ordered-alists x y z))))

(defthm alistp-gen-sort-the-alist-by-merge
  (implies (alistp-gen x)
           (alistp-gen (sort-the-alist-by-merge x z))))

(verify-guards sort-the-alist-by-merge
               :hints (("Goal" :do-not-induct t)))

(defun cluster-sort-by-merge (flg x taxon-index-alist)
  (declare (xargs :guard (and (good-taxon-index-halist
                               taxon-index-alist)
                              (taspip flg x)
                              (subset (mytips x)
                                       (get-taxa-from-taxon-index
                                        taxon-index-alist)))
                  :measure (make-ord (1+ (acl2-count x))
                                     1
                                     (if flg 1 0))
                  :verify-guards nil))
   (if (atom x)
       x
     (if flg ; top tree
         (let* ((list-of-sorted-elements
                 (cluster-sort-by-merge
                  nil x taxon-index-alist))
                (least-key-value-elements
                 (pair-key-with-value list-of-sorted-elements)))
           (strip-cdrs-gen
            (sort-the-alist-by-merge least-key-value-elements
                                     taxon-index-alist)))
       (hons (cluster-sort-by-merge t (car x) taxon-index-alist)
             (cluster-sort-by-merge nil (cdr x) taxon-index-alist)))
     ))


(defthm consp-through-sort-the-alist-by-merge
  (implies (consp x)
           (consp (sort-the-alist-by-merge x tia))))

(defthm consp-through-cluster-sort-by-merge
  (implies (consp x)
           (consp (cluster-sort-by-merge flg x tia))))

(defthm taspip-strip-cdrs-taspip-merge
  (implies (and (taspip nil (strip-cdrs-gen x))
                (taspip nil (strip-cdrs-gen y)))
           (taspip nil (strip-cdrs-gen
                        (merge-sort-of-ordered-alists
                         x y tia)))))

(defthm consp-through-merge
  (implies (or (consp x)
               (consp y))
           (consp (merge-sort-of-ordered-alists x y tia))))

(defthm taspip-strip-cdrs-taspip-sort
  (implies (taspip flg (strip-cdrs-gen x))
           (taspip flg (strip-cdrs-gen
                        (sort-the-alist-by-merge x tia)))))


;(defthm taspip-nil-pair-sort-still-taspip
;  (implies (and (taspip nil x)
;                (consp x))
;           (taspip flg (strip-cdrs-gen
;                        (sort-the-alist-by-merge
;                         (pair-key-with-value x) tia)))))

(defthm taspip-through-cluster-sort-by-merge
  (implies (taspip flg x)
           (taspip flg (cluster-sort-by-merge
                        flg x tia))))

;(defthm taspip-gives-subset-strip-cars-pair-of-mytips
;  (implies (taspip flg x)
;           (subset (strip-cars-gen
;                    (pair-key-with-value x))
;                   (mytips x))))


(defthm subset-mytips-strip-cdrs-merge
  (implies (and (subset (mytips (strip-cdrs-gen
                                 x)) z)
                (subset (mytips (strip-cdrs-gen y)) z))
           (subset (mytips (strip-cdrs-gen
                            (merge-sort-of-ordered-alists
                             x y tia))) z)))

(defthm subset-mytips-strip-cdrs-sort-pair
  (implies (subset (mytips x) y)
           (subset (mytips (strip-cdrs-gen
                            (sort-the-alist-by-merge
                             x tia)))
                   y))
  :hints (("Subgoal *1/5'''" :in-theory
           (disable subset-mytips-evens-gen-mytips)
           :use (:instance subset-mytips-evens-gen-mytips
                           (x (cons x1 x2))))
          ("Subgoal *1/4'5'" :in-theory
           (disable subset-mytips-evens-gen-mytips)
           :use (:instance subset-mytips-evens-gen-mytips
                           (x x2)))
          ("Subgoal *1/3''" :in-theory
           (disable subset-mytips-evens-gen-mytips)
           :use (:instance subset-mytips-evens-gen-mytips))
))


(defthm subset-mytips-cluster-sort-mytips-x
  (implies (taspip flg x)
           (subset (mytips (cluster-sort-by-merge flg x tia))
                   (mytips x)))
  :hints (("Subgoal *1/3''" :in-theory
           (disable subset-mytips-strip-cdrs-sort-pair)
           :use (:instance subset-mytips-strip-cdrs-sort-pair
                           (x (pair-key-with-value
                               (cluster-sort-by-merge nil x tia)))
                           (y (mytips x))))
          ("Subgoal *1/3'4'" :in-theory
           (disable subset-mytips-gives-subset-pair)
           :use (:instance subset-mytips-gives-subset-pair
                           (x (cluster-sort-by-merge nil x tia))
                           (y (mytips x))))
                           ))

(defthmd strip-cars-pair-cluster-subset-mytips
  (implies (taspip flg x)
           (subset (strip-cars-gen (pair-key-with-value x))
                   (mytips x))))

(verify-guards
 cluster-sort-by-merge
 :hints (("Goal" :do-not-induct t)
         ("Subgoal 4'" :in-theory
          (disable subset-mytips-gives-subset-pair
                  keys-from-pair-key-subset-x
                  subset-mytips-cluster-sort-mytips-x)
          :use
          (:instance strip-cars-pair-cluster-subset-mytips
                     (x (cluster-sort-by-merge
                         nil x taxon-index-alist))))
         ("Subgoal 4''" :use
          (:instance subset-mytips-cluster-sort-mytips-x
                     (flg nil)
                     (tia taxon-index-alist)))
         ))

(defun order-by-merge-help (flg x taxon-index-alist)
  (declare (xargs :guard (and (good-taxon-index-halist
                               taxon-index-alist)
                              (taspip flg x)
                              (subset (mytips x)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))))
  (cluster-sort-by-merge flg x taxon-index-alist))

(defun order-by-merge (x taxon-index-alist)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;   Returns the structurally unchanged input but with leaves ordered according
;   to the mapping given.~/
;   ~/
;   Arguments:
;      (1) x - a tree
;      (2) taxon-index-alist - a mapping of taxa names to integers

;   Details: The leaves in the tree must all be represented in the mapping
;            given.  Ordering is achieved using a merge sort algorithm.
;            Consider also order-by-insertion."
  (declare (xargs :guard (and (good-taxon-index-halist
                               taxon-index-alist)
                              (taspip t x)
                              (subset (mytips x)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))))
  (order-by-merge-help t x taxon-index-alist))

(defun order-by-merge-one-level (x taxon-index-alist)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;   Returns the structurally unchanged input but with top-level subtrees
;   ordered according to the mapping given.~/
;   ~/
;   Arguments:
;      (1) x - a tree
;      (3) taxon-index-alist - a mapping of taxa names to integers

;   Details: The leaves in the tree must all be represented in the mapping
;            given.  Ordering is achieved using a merge sort algorithm.
;            The tree produced will only be fully ordered if each of the
;            top-level trees are intially ordered.
;            Consider also order-by-insertion-one-level."
  (declare (xargs :guard (and (good-taxon-index-halist taxon-index-alist)
                              (taspip t x)
                              (subset (mytips x)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))))
  (let ((least-key-value-elements (pair-key-with-value x)))
    (strip-cdrs-gen
     (sort-the-alist-by-merge least-key-value-elements
                              taxon-index-alist))))

; now for correctness

(defthm orderedp-nil-through-merge
  (implies (and (orderedp nil (strip-cdrs-gen x) tia)
                (orderedp nil (strip-cdrs-gen y) tia))
           (orderedp nil (strip-cdrs-gen
                          (merge-sort-of-ordered-alists
                           x y tia))
                     tia)))

(defthm orderedp-nil-through-sort
  (implies (orderedp nil (strip-cdrs-gen x) tia)
           (orderedp nil (strip-cdrs-gen
                          (sort-the-alist-by-merge x tia))
                     tia)))

(defthm valid-pairing-through-merge-alst
  (implies (and (valid-pairing x)
                (valid-pairing y))
           (valid-pairing (merge-sort-of-ordered-alists
                           x y tia))))


(defthm valid-pairing-through-sort-the-alist-by-merge
  (implies (valid-pairing x)
           (valid-pairing (sort-the-alist-by-merge x tia))))

(local
(defthm not-consp-strip-cars-gen-not-consp-x
  (implies (and (not (consp (strip-cars-gen x)))
                (alistp-gen x))
           (not (consp x)))
  :rule-classes :forward-chaining)
)

(defthm car-strip-cars-merge-or
  (implies (and (alistp-gen x)
                (alistp-gen y)
                (consp x)
                (consp y))
           (or (equal (caar
                       (merge-sort-of-ordered-alists
                        x y tia))
                      (caar x))
               (equal (caar
                       (merge-sort-of-ordered-alists
                        x y tia))
                      (caar y))))
  :rule-classes nil)

;; this is where car-strip-cars-gen was

(defthm both-less-merge-less
  (implies (and (alistp-gen x)
                (alistp-gen y)
                (consp x)
                (consp y)
                (<= (assoc-hqual (caar x) tia)
                    (assoc-hqual z tia))
                (<= (assoc-hqual (caar y) tia)
                    (assoc-hqual z tia)))
           (<= (assoc-hqual (caar (merge-sort-of-ordered-alists
                                   x y tia)) tia)
               (assoc-hqual z tia))))

(defthm ordered-list-merge
  (implies (and (alistp-gen x)
                (alistp-gen y)
                (ordered-list (strip-cars-gen x) tia)
                (ordered-list (strip-cars-gen y) tia))
           (ordered-list (strip-cars-gen
                          (merge-sort-of-ordered-alists
                           x y tia)) tia))
  :hints (("Subgoal *1/8.1.1" :use
           (:instance car-strip-cars-merge-or
                      (y y2)))
          ("Subgoal *1/8.1" :cases ((consp y2)))
          ("Subgoal *1/5.1" :cases ((consp x2)))
          ("Subgoal *1/5.1.1" :use
           (:instance car-strip-cars-merge-or
                      (x x2)))
          ))

(defthmd alistp-gen-through-cons
  (implies (and (alistp-gen y)
                (consp x))
           (alistp-gen (cons x y))))

(defthm ordered-list-strips-cars-of-sort
  (implies (alistp-gen alst)
           (ordered-list (strip-cars-gen
                          (sort-the-alist-by-merge alst tia))
                         tia)))

(defthm len-merge-alsts
  (equal (len (merge-sort-of-ordered-alists
               x y tia))
         (+ (len (double-rewrite x)) (len (double-rewrite y)))))

(defthm len-evens-gen-of-even-len
  (implies (evenp (len (double-rewrite x)))
           (equal (len (evens-gen x))
                  (/ (len (double-rewrite x)) 2))))

(defthm len-evens-gen-of-odd-len
  (implies (oddp (len (double-rewrite x)))
           (equal (len (evens-gen x))
                  (+ 1 (/ (- (len (double-rewrite x)) 1) 2)))))

(defthm len-sort-the-alist
  (equal (len (sort-the-alist-by-merge alst tia))
         (len (double-rewrite alst)))
  :hints (("Subgoal *1/3'5'" :cases ((evenp (len alst2))))
          ))

(defthm len-cluster-sort-by-merge
  (equal (len (cluster-sort-by-merge flg x tia))
         (len (double-rewrite x))))

(defthm tree-listp-and-consp-gives-cdr
  (implies (and (tree-listp x)
                (consp x))
           (tree-listp (cdr x))))

(defthm tree-listp-through-merge
  (implies (and (tree-listp (strip-cdrs-gen x))
                (tree-listp (strip-cdrs-gen y)))
           (tree-listp (strip-cdrs-gen
                        (merge-sort-of-ordered-alists
                         x y tia)))))


(defthm tree-listp-through-evens-gen
  (implies (tree-listp (strip-cdrs-gen x))
           (tree-listp (strip-cdrs-gen (evens-gen x)))))

(defthm tree-listp-through-sort-by-merge
  (implies (tree-listp (strip-cdrs-gen alst))
           (tree-listp (strip-cdrs-gen
                        (sort-the-alist-by-merge
                         alst tia)))))

(defthm tree-listp-through-cluster-sort-by-merge
  (implies (and (tree-listp x)
                (taspip flg x)
                (good-taxon-index-halist taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index
                         taxon-index-alist)))
           (tree-listp
            (cluster-sort-by-merge
             flg x taxon-index-alist))))

(defthm treep-through-cluster-sort-by-merge
  (implies (and (treep x)
                (taspip flg x)
                (good-taxon-index-halist taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index
                         taxon-index-alist)))
           (treep
            (cluster-sort-by-merge
             flg x taxon-index-alist)))
  :hints (("Subgoal *1/19''" :expand (treep x))
))


;; major properties of order-by-merge
(defthm taspip-through-order-by-merge
  (implies (taspip flg x)
           (taspip flg (order-by-merge-help flg x tia))))

(defthm subset-mytips-through-order-by-merge
  (implies (taspip flg x)
           (subset (mytips (order-by-merge-help flg x tia))
                   (mytips x))))

(defthm order-by-merge-gives-orderedp
  (implies (and (taspip flg x)
                (good-taxon-index-halist
                 taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index
                         taxon-index-alist)))
           (orderedp flg
                     (order-by-merge-help flg x taxon-index-alist)
                     taxon-index-alist)))

(defthm treep-through-order-by-merge
  (implies (and (treep x)
                (taspip flg x)
                (good-taxon-index-halist taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index
                         taxon-index-alist)))
           (treep
            (order-by-merge-help
             flg x taxon-index-alist))))

(defthm tree-listp-through-order-by-merge
  (implies (and (tree-listp x)
                (taspip flg x)
                (good-taxon-index-halist taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index
                         taxon-index-alist)))
           (tree-listp
            (order-by-merge-help
             flg x taxon-index-alist))))


(in-theory (disable order-by-merge-help))

(defun order-each-by-merge (input-trees taxon-index-alist)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;   Returns a list where each of the trees in the input list has been
;   structurally unchanged but now has leaves ordered according
;   to the mapping given.~/
;   ~/
;   Arguments:
;      (1) input-trees - a list of trees
;      (2) taxon-index-alist - a mapping of taxa names to integers
;      (3) length-taxon-index-alist - a number larger than any value in the
;                                     mapping

;   Details: The leaves in each of the trees must all be represented in the
;            mapping given.  Ordering is achieved using a merge sort
;            algorithm. Consider also order-each-by-insertion."
  (declare (xargs :guard (and (good-taxon-index-halist
                               taxon-index-alist)
                              (taspip nil input-trees)
                              (subset (mytips input-trees)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))))
  (if (atom input-trees)
      nil
    (cons (order-by-merge (car input-trees) taxon-index-alist)
          (order-each-by-merge (cdr input-trees)
                               taxon-index-alist))))

;It would be great to get the last property below through, but I haven't
;taken the time to do so
;
;; (skip-proofs
;;  (defthm SKIP-perm-mytips-cluster-sort-by-merge
;;    (implies (taspip flg x)
;;             (perm (mytips (cluster-sort-by-merge flg x tia))
;;                   (mytips x))))
;; )

;; (defthm perm-mytips-order-by-merge
;;   (implies (taspip flg x)
;;            (perm (mytips (order-by-merge-help flg x tia))
;;                  (mytips x)))
;;   :hints (("Goal" :in-theory (enable order-by-merge-help))))

#|
(order-by-merge t
                '(b c (d (E h) (p g (s (r t)))))
                (build-fast-alist-from-alist
                 (element-to-number '(a b c d e g h p r s t) 0)
                 'tia))
|#
