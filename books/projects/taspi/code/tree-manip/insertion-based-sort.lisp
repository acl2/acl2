;; This implements an insertion sort at each level
;; Recursively, each level is sorted, then the first taxon
;; of each term is determined and paired to its term,
;; the first taxons are found in the taxon-index-alist
;; and the minimum is consed to the front, thus creating
;; the term

(in-package "ACL2")
(include-book "sort-help")

;; for each first taxon, find the min given the taxon-index-alist
;; current-min first passed in as length of tia,
;; and thus no entry with that key
(defun get-min-key (alst key current-min taxon-index-alist)
  (declare (xargs :guard (and (rationalp current-min)
                              (good-taxon-index-halist
                               taxon-index-alist)
                              (alistp-gen alst)
                              (subset (strip-cars-gen alst)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))
                 ))
  (if (atom alst)
      key
    (let ((index (cdr (het (caar alst) taxon-index-alist))))
      (if (< index current-min)
          (get-min-key (cdr alst) (caar alst) index taxon-index-alist)
        (get-min-key (cdr alst) key current-min taxon-index-alist)))))

(defthm get-min-key-when-not-consp
  (implies (not (consp alst))
          (equal (get-min-key alst key cur-min tia)
                 key)))

(defthm get-min-key-of-consp
  (equal (get-min-key (cons first rest) key cur-min tia)
         (let ((index (cdr (het (car first) tia))))
           (if (< index cur-min)
               (get-min-key rest (car first) index tia)
             (get-min-key rest key cur-min tia)))))

(dis+ind get-min-key)

(defun greater-all (x list)
  (declare (xargs :guard (and (rationalp x)
                              (good-taxon-index-halist list))))
  (if (consp list)
      (and (< (cdar list) x)
           (greater-all x (cdr list)))
    t))

(defthm greater-all-when-not-consp
  (implies (not (consp list))
           (equal (greater-all x list)
                  t)))

(defthm greater-all-of-consp
  (equal (greater-all x (cons first rest))
         (and (< (cdr first) x)
              (greater-all x rest))))

(dis+ind greater-all)

(defthm member-gen-get-taxa-with-greater-all-gives-<cur-min
  (implies (and (member-gen x (get-taxa-from-taxon-index tia))
                (greater-all cur-min tia))
           (< (cdr (assoc-hqual x tia)) cur-min)))

(defthm get-min-key-not-key-member-strip
  (implies (not (equal (get-min-key alst key cur-min tia)
                       key))
           (member-gen (get-min-key alst key cur-min tia)
                       (strip-cars-gen alst))))

(defthm greater-all-gives-member-key
  (implies (and (consp alst)
                (greater-all cur-min tia)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index
                         tia)))
           (member-gen (get-min-key alst key cur-min tia)
                       (strip-cars-gen alst))))


;; build up the alist of terms into a sorted alst
(defun sort-the-alist-by-insertion
  (alst taxon-index-alist length-taxon-index-alist)
  (declare (xargs :guard (and (good-taxon-index-halist
                               taxon-index-alist)
                              (alistp-gen alst)
                              (subset (strip-cars-gen alst)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist))
                              (rationalp length-taxon-index-alist)
                              (greater-all length-taxon-index-alist
                                           taxon-index-alist)
                              (not (member-gen nil (strip-cars-gen alst))))))
  (if (atom alst)
      nil
    (if (mbt (and (greater-all length-taxon-index-alist
                               taxon-index-alist)
                  (not (member-gen nil (strip-cars-gen alst)))
                  (alistp-gen alst)
                  (subset (strip-cars-gen alst)
                          (get-taxa-from-taxon-index
                           taxon-index-alist))
                  (good-taxon-index-halist
                   taxon-index-alist)))
        (let ((min-key (get-min-key alst nil
                                    length-taxon-index-alist
                                    taxon-index-alist)))
          (hons (assoc-hqual min-key alst)
                (sort-the-alist-by-insertion (del-pair min-key alst)
                                taxon-index-alist
                                length-taxon-index-alist)))
      nil)))

(defthm sort-the-alist-by-insertion-when-not-consp
  (implies (not (consp alst))
           (equal (sort-the-alist-by-insertion alst tia len-tia)
                  nil)))

(defthm sort-the-alist-by-insertion-of-consp
  (implies (consp alst)
           (equal (sort-the-alist-by-insertion alst tia len-tia)
                  (if (and (greater-all len-tia tia)
                           (not (member-gen nil (strip-cars-gen alst)))
                           (alistp-gen alst)
                           (subset (strip-cars-gen alst)
                            (get-taxa-from-taxon-index tia))
                           (good-taxon-index-halist tia))
                      (let ((min-key (get-min-key
                                      alst nil
                                      len-tia
                                      tia)))
                        (hons (assoc-hqual min-key alst)
                              (sort-the-alist-by-insertion
                               (del-pair min-key alst)
                               tia
                               len-tia)))
                    nil))))

(dis+ind sort-the-alist-by-insertion)

;; do the recursion for each level
(defun cluster-sort-by-insertion
  (flg x taxon-index-alist length-taxon-index-alist)
   (declare (xargs :guard (and (good-taxon-index-halist taxon-index-alist)
                               (taspip flg x)
                               (rationalp length-taxon-index-alist)
                               (greater-all length-taxon-index-alist
                                            taxon-index-alist)
                               (subset (mytips x)
                                       (get-taxa-from-taxon-index
                                        taxon-index-alist))
                               )
                   :measure (make-ord (1+ (acl2-count x))
                                     1
                                     (if flg 1 0))
                   :verify-guards nil))
   (if flg
       (if (atom x)
           x
         (let* ((list-of-sorted-elements
                 (cluster-sort-by-insertion
                  nil x taxon-index-alist
                  length-taxon-index-alist))
                (least-key-value-elements
                 (pair-key-with-value list-of-sorted-elements)))
           (strip-cdrs-gen (sort-the-alist-by-insertion
                            least-key-value-elements
                            taxon-index-alist
                            length-taxon-index-alist))))
   ;; creating list where each element is sorted
   (if (atom x)
       x ;will be nil if (taspip flg x)
     (hons (cluster-sort-by-insertion
            t (car x) taxon-index-alist length-taxon-index-alist)
           (cluster-sort-by-insertion
            nil (cdr x) taxon-index-alist
            length-taxon-index-alist))))
)

(defthm cluster-sort-by-insertion-when-not-consp
  (implies (not (consp x))
           (equal (cluster-sort-by-insertion flg x tia len-tia)
                  x)))

(defthm cluster-sort-by-insertion-of-consp
  (equal (cluster-sort-by-insertion flg (cons first rest) tia len-tia)
         (if flg
             (let* ((list-of-sorted-elements
                     (cluster-sort-by-insertion nil
                                   (cons first rest)
                                   tia len-tia))
                    (least-key-value-elements
                     (pair-key-with-value
                      list-of-sorted-elements)))
               (strip-cdrs-gen (sort-the-alist-by-insertion
                                least-key-value-elements
                                tia
                                len-tia)))
           (hons (cluster-sort-by-insertion t first tia len-tia)
                 (cluster-sort-by-insertion nil rest tia len-tia)))))

(dis+ind cluster-sort-by-insertion)

(defthm taspip-nil-strip-cdrs-taspip-nil-sort
  (implies (and (greater-all len-tia tia)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index tia))
                (taspip nil (strip-cdrs-gen alst)))
           (taspip nil (strip-cdrs-gen
                        (sort-the-alist-by-insertion
                         alst tia len-tia)))))

(defthm consp-gives-consp-sort
  (implies (and (greater-all len-tia tia)
                (good-taxon-index-halist tia)
                (not (member-gen nil (strip-cars-gen x)))
                (alistp-gen x)
                (subset (strip-cars-gen x)
                        (get-taxa-from-taxon-index tia))
                (consp x))
           (consp (sort-the-alist-by-insertion x tia len-tia))))


(defthm subset-mytips-sort
  (subset (mytips (strip-cdrs-gen
                   (sort-the-alist-by-insertion x tia len-tia)))
          (mytips (strip-cdrs-gen x))))

(defthm subset-mytips-cluster-sort-by-insertion
  (subset (mytips (cluster-sort-by-insertion flg x tia len-tia))
          (mytips x))
  :hints (("Subgoal *1/2'" :expand ((cluster-sort-by-insertion
                                     flg x tia len-tia)
                                    (cluster-sort-by-insertion
                                     nil x tia len-tia)))
          ("Subgoal *1/2'''" :in-theory
           (disable subset-mytips-sort
                    subset-mytips-strip-cdrs-pair)
           :use ((:instance subset-mytips-sort
                           (x (pair-key-with-value
                               (cluster-sort-by-insertion
                                nil x tia len-tia))))
                 (:instance subset-mytips-strip-cdrs-pair
                            (x
                             (cluster-sort-by-insertion
                              nil x tia len-tia)))))))

(defthm taspip-cluster-sort-by-insertion
  (implies (and (taspip flg x)
                (greater-all len-tia tia)
                (good-taxon-index-halist tia)
                (subset (mytips x)
                        (get-taxa-from-taxon-index tia))
                (good-taxon-index-halist tia)
                (consp x))
           (and (taspip flg (cluster-sort-by-insertion
                             flg x tia len-tia))
                (consp (cluster-sort-by-insertion
                        flg x tia len-tia))))
  :hints (("Goal" :induct (cluster-sort-by-insertion
                           flg x tia len-tia))
          ("Subgoal *1/1.2" :expand (cluster-sort-by-insertion
                                     flg x tia len-tia)
           :in-theory
           (disable taspip-subset-strip-cars-mytips
                    subset-mytips-cluster-sort-by-insertion
                    keys-from-pair-key-subset-x)
           :use ((:instance taspip-subset-strip-cars-mytips
                            (x (cluster-sort-by-insertion
                                nil x tia len-tia))
                            (flg nil))
                 (:instance subset-mytips-cluster-sort-by-insertion
                            (flg nil))))
          ("Subgoal *1/1.1" :expand (cluster-sort-by-insertion
                                     flg x tia len-tia))
          ("Subgoal *1/1.1.1'"
           :in-theory
           (disable taspip-subset-strip-cars-mytips
                    subset-mytips-cluster-sort-by-insertion
                    keys-from-pair-key-subset-x)
            :use ((:instance taspip-subset-strip-cars-mytips
                            (x (cluster-sort-by-insertion nil x tia len-tia))
                            (flg nil))
                  (:instance subset-mytips-cluster-sort-by-insertion
                            (flg nil))))
))

(defthm member-gen-alistp-gen-gives-consp
  (implies (and (member-gen x (strip-cars-gen alst))
                (alistp-gen alst))
           (consp (assoc-hqual x alst))))

(defthm alistp-gen-sort
  (implies (alistp-gen alst)
           (alistp-gen
            (sort-the-alist-by-insertion alst tia len-tia))))

(verify-guards
 cluster-sort-by-insertion
 :hints (("Goal" :do-not-induct t)
         ("Subgoal 4" :in-theory
          (disable taspip-subset-strip-cars-mytips
                   subset-mytips-cluster-sort-by-insertion
                   keys-from-pair-key-subset-x)
          :use ((:instance taspip-subset-strip-cars-mytips
                           (x (cluster-sort-by-insertion
                              nil x
                               taxon-index-alist
                               length-taxon-index-alist))
                           (flg nil))
                (:instance subset-mytips-cluster-sort-by-insertion
                           (flg nil)
                           (tia taxon-index-alist)
                           (len-tia length-taxon-index-alist))
                ))
         ("Subgoal 4''" :in-theory (disable not-member-subset)
          :use (:instance not-member-subset
                          (x nil)
                          (y (mytips x))
                          (z (strip-cars-gen
                              (pair-key-with-value
                               (cluster-sort-by-insertion
                                nil x
                                taxon-index-alist
                                length-taxon-index-alist))))))
))

(defun order-by-insertion-help
  (flg x taxon-index-alist length-taxon-index-alist)
  (declare (xargs :guard (and (taspip flg x)
                              (good-taxon-index-halist
                               taxon-index-alist)
                              (subset (mytips x)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist))
                              (rationalp length-taxon-index-alist)
                              (greater-all length-taxon-index-alist
                                           taxon-index-alist))))
  (cluster-sort-by-insertion
   flg x taxon-index-alist length-taxon-index-alist))

(defun max-list-helper (curMax list)
  (declare (xargs :guard t))
  (if (consp list)
      (if (and (rationalp curMax)
               (rationalp (car list)))
          (if (< curMax (car list))
              (max-list-helper (car list) (cdr list))
            (max-list-helper curMax (cdr list)))
        curMax)
    curMax))

(defun max-list (list)
  (declare (xargs :guard t))
  (if (consp list)
      (max-list-helper (car list) (cdr list))
    nil))

(defun order-by-insertion (x taxon-index-alist)

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
;            given.  Ordering is achieved using an insertion sort algorithm.
;            Consider also order-by-merge."
  (declare (xargs :guard (and (taspip t x)
                              (good-taxon-index-halist
                               taxon-index-alist)
                              (subset (mytips x)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))))
  (let ((max (max-list (strip-cdrs-gen taxon-index-alist))))
    (if (and (rationalp max)
             (greater-all (1+ max) taxon-index-alist))
        (order-by-insertion-help t x taxon-index-alist (1+ max))
      "Error: Need valid taxon-index-alist in order-by-insertion")))


(defun order-by-insertion-one-level (x taxon-index-alist)

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
;            given.  Ordering is achieved using an insertion sort algorithm.
;            The tree produced will only be fully ordered if each of the
;            top-level trees are intially ordered.
;            Consider also order-by-merge-one-level."
  (declare (xargs :guard (and (taspip t x)
                              (good-taxon-index-halist
                               taxon-index-alist)
                              (subset (mytips x)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist)))))
  (let ((max (max-list (strip-cdrs-gen taxon-index-alist))))
    (if (rationalp max)
        (let ((least-key-value-elements (pair-key-with-value x)))
          (if (greater-all (1+ max) taxon-index-alist)
              (hopy (strip-cdrs-gen (sort-the-alist-by-insertion
                               least-key-value-elements
                               taxon-index-alist
                               (1+ max))))
            "Error: Need greater-all in order-by-insertion-one-level"))
      "Error: Need rational max in order-by-insertion-one-level")))


;; now for correctness

(defthm ordered-nil-strip-cdrs-ordered-nil-strip-sort
  (implies (orderedp nil (strip-cdrs-gen alst) tia)
           (orderedp nil (strip-cdrs-gen
                          (sort-the-alist-by-insertion
                           alst tia len-tia)) tia)))

(defthm ordered-nil-through-sort
  (implies (orderedp nil x tia)
           (orderedp nil (strip-cdrs-gen
                          (sort-the-alist-by-insertion
                           (pair-key-with-value x)
                           tia len-tia)) tia)))

(defthm cluster-t-doesnt-change-ordered-nil
  (implies (orderedp nil (cluster-sort-by-insertion
                          nil x tia len-tia) tia)
           (orderedp nil (cluster-sort-by-insertion
                          t x tia len-tia) tia))
  :hints (("Goal" :expand (cluster-sort-by-insertion
                          t x tia len-tia))))


(defthm assoc-min-key-when-not-input
  (implies (not (equal (get-min-key alst key len-tia tia)
                       key))
           (<= (cdr (assoc-hqual (get-min-key alst key len-tia tia) tia))
               len-tia)))

(defthm if-key-cur-min-pair
  (implies (equal (cdr (assoc-hqual key tia)) cur-min)
           (<= (cdr (assoc-hqual
                     (get-min-key alst key cur-min tia) tia))
               cur-min)))

(defthm exists-key-<-then-less
  (implies (and (member-gen x (strip-cars-gen alst))
                (alistp-gen alst)
                (< (cdr (assoc-hqual x tia))
                   len-tia))
           (< (cdr (assoc-hqual
                    (get-min-key alst key len-tia tia) tia))
              len-tia))
  :hints (("Subgoal *1/4.1.2'" :in-theory
           (disable if-key-cur-min-pair)
           :use (:instance if-key-cur-min-pair
                           (key alst3)
                           (cur-min
                            (cdr
                             (hons-assoc-equal alst3 tia)))
                           (alst alst2)))
          ("Subgoal *1/4.1.1" :in-theory
           (disable if-key-cur-min-pair)
           :use (:instance if-key-cur-min-pair
                           (key alst3)
                           (cur-min
                            (cdr
                             (hons-assoc-equal alst3 tia)))
                           (alst alst2)))
          ("Subgoal *1/2.1'''" :in-theory
           (disable if-key-cur-min-pair)
           :use (:instance if-key-cur-min-pair
                           (key alst3)
                           (cur-min
                            (cdr
                             (hons-assoc-equal alst3 tia)))
                           (alst alst2)))))

(defthm greater-all-min-key-<
  (implies (and (good-taxon-index-halist tia)
                (alistp-gen alst)
                (consp alst)
                (greater-all len-tia tia)
                (subset (strip-cars-gen
                         alst)
                        (get-taxa-from-taxon-index tia)))
           (< (cdr (assoc-hqual
                     (get-min-key alst key len-tia tia) tia))
               len-tia))
  :hints (("Subgoal *1/5.1''" :in-theory
           (disable member-gen-get-taxa-with-greater-all-gives-<cur-min)
           :use (:instance member-gen-get-taxa-with-greater-all-gives-<cur-min
                           (x alst3)
                           (cur-min len-tia)))
          ("Subgoal *1/3.1''" :in-theory
           (disable
            if-key-cur-min-pair
            member-gen-get-taxa-with-greater-all-gives-<cur-min)
           :use ((:instance if-key-cur-min-pair
                           (key alst3)
                           (cur-min
                            (cdr
                             (hons-assoc-equal alst3 tia)))
                           (alst alst2))
                 (:instance
                  member-gen-get-taxa-with-greater-all-gives-<cur-min
                  (x alst3)
                  (cur-min len-tia))))
                    ))


(defthm valid-pairing-through-sort
  (implies (valid-pairing alst)
           (valid-pairing (sort-the-alist-by-insertion
                           alst tia len-tia))))


(defthm gives-get-min-key-less-all-members
  (implies (and (alistp-gen alst)
                (member-gen x (strip-cars-gen alst))
                (equal (get-min-key alst key cur-min tia)
                       key)
                (equal (cdr (assoc-hqual key tia))
                       cur-min))
           (<= (cdr (assoc-hqual key tia))
               (cdr (assoc-hqual x tia)))))

(defun check-less (x list tia)
  (if (consp list)
      (and (<= (cdr (assoc-hqual x tia))
               (cdr (assoc-hqual (caar list) tia)))
           (check-less x (cdr list) tia))
    t))

(defun get-min-key2 (alst key tia)
  (declare (xargs :guard
                  (and (alistp-gen alst)
                       (good-taxon-index-halist tia)
                       (member-gen key
                                   (get-taxa-from-taxon-index tia))
                       (subset (strip-cars-gen alst)
                               (get-taxa-from-taxon-index tia)))))
  (if (consp alst)
      (if (< (cdr (assoc-hqual (caar alst) tia))
             (cdr (assoc-hqual key tia)))
          (get-min-key2 (cdr alst) (caar alst) tia)
        (get-min-key2 (cdr alst) key tia))
    key))

(defthm pair-key-cur-min-same-as-get-min2
  (implies (equal (cdr (assoc-hqual key tia))
                  cur-min)
           (equal (get-min-key alst key cur-min tia)
                  (get-min-key2 alst key tia))))

(defthm get-min-key=key-min-key2-gen
  (implies (and (good-taxon-index-halist tia)
                (consp alst)
                (alistp-gen alst)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index tia))
                (greater-all len-tia tia)
                (member-gen x (strip-cars-gen alst)))
           (equal (get-min-key alst (caar alst)
                               (cdr (assoc-hqual (caar alst)
                                                 tia))
                               tia)
                  (get-min-key2 (cdr alst) (caar alst) tia))))

(defthm not-equal-get-min2
  (implies (and (member-gen key
                            (get-taxa-from-taxon-index tia))
                (alistp-gen alst)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index tia))
                (not (equal (get-min-key2 alst key tia)
                            key)))
           (< (cdr (assoc-hqual (get-min-key2 alst key tia)
                                tia))
              (cdr (assoc-hqual key tia)))))

(defthm get-min2-<
  (implies (and (good-taxon-index-halist tia)
                (alistp-gen alst)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index tia)))
           (<= (cdr (assoc-hqual
                     (get-min-key2 alst key tia) tia))
               (cdr (assoc-hqual key tia))))
  :hints (("Subgoal *1/6'5'"
           :cases ((equal (get-min-key2 alst2 alst3 tia) alst3)))
          ("Subgoal *1/6.2" :in-theory
           (disable not-equal-get-min2)
           :use (:instance not-equal-get-min2
                           (alst alst2)
                           (key alst3)))
          ("Subgoal *1/2.1"
           :cases ((equal (get-min-key2 alst2 alst3 tia) alst3)))
          ("Subgoal *1/2.1.2" :in-theory
           (disable not-equal-get-min2)
           :use (:instance not-equal-get-min2
                           (alst alst2)
                           (key alst3)))
))

(defthm get-min-gives-check-less-strip-cars
  (implies (and (good-taxon-index-halist tia)
                (alistp-gen alst)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index tia)))
           (check-less (get-min-key2 alst key tia)
                       alst tia))
  :hints (("Subgoal *1/6.1''" :in-theory (disable get-min2-<)
           :use (:instance get-min2-<
                           (alst alst2)))
))

(defthm check-less-gives-less=-member
  (implies (and (member-gen x (strip-cars-gen alst))
                (check-less key alst tia))
           (<= (cdr (assoc-hqual key tia))
               (cdr (assoc-hqual x tia)))))

(defthm get-min-key-correct
  (implies (and (good-taxon-index-halist tia)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index tia))
                (member-gen x (strip-cars-gen alst))
                (alistp-gen alst)
                (greater-all len-tia tia))
           (<= (cdr (assoc-hqual
                     (get-min-key alst key len-tia tia) tia))
               (cdr (assoc-hqual x tia))))
)


(defthm subset-strip-cars-strip-cars
  (implies (greater-all len-tia tia)
           (subset
            (strip-cars-gen
             (sort-the-alist-by-insertion alst tia len-tia))
            (strip-cars-gen alst))))


(defthm sort-correct
  (implies (and (good-taxon-index-halist tia)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index tia))
                (greater-all len-tia tia)
                (alistp-gen alst))
           (ordered-list (strip-cars-gen
                          (sort-the-alist-by-insertion
                           alst tia len-tia))
                         tia))
  :hints (("Subgoal *1/4''" :in-theory
           (disable get-min-key-correct)
           :use (:instance
                 get-min-key-correct
                 (x (car (strip-cars-gen
                          (sort-the-alist-by-insertion
                           (del-pair
                            (get-min-key alst nil len-tia tia)
                            alst)
                           tia len-tia))))
                 (key nil)))
          ("Subgoal *1/4'4'" :in-theory
           (disable member-gen-car-strip-cars
                    subset-strip-cars-strip-cars)
           :use ((:instance member-gen-car-strip-cars
                           (x (sort-the-alist-by-insertion
                               (del-pair
                                (get-min-key alst nil len-tia tia)
                                alst)
                               tia len-tia))
                           (y (strip-cars-gen alst)))
                 (:instance subset-strip-cars-strip-cars
                            (alst (del-pair
                                   (get-min-key alst nil len-tia tia)
                                   alst)))))
))

(defthm orderedp-cluster
  (implies (and (taspip flg x)
                (good-taxon-index-halist taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index taxon-index-alist))
                (rationalp length-taxon-index-alist)
                (greater-all length-taxon-index-alist
                             taxon-index-alist))
           (orderedp flg
                     (cluster-sort-by-insertion
                      flg x taxon-index-alist
                      length-taxon-index-alist)
                     taxon-index-alist))
  :hints (("Subgoal *1/3.2" :in-theory
           (disable sort-the-alist-by-insertion-of-consp)
           :expand (cluster-sort-by-insertion
                    flg x taxon-index-alist
                    length-taxon-index-alist))
          ("Subgoal *1/3.2'" :in-theory (disable sort-correct)
           :use (:instance
                 sort-correct
                 (alst (pair-key-with-value
                        (cluster-sort-by-insertion
                         nil x taxon-index-alist
                         length-taxon-index-alist)))
                 (tia taxon-index-alist)
                 (len-tia length-taxon-index-alist)))
          ("Subgoal *1/3.1" :expand (cluster-sort-by-insertion
                                     flg x taxon-index-alist
                                     length-taxon-index-alist))
          ))

(defthm tree-listp-through-del-pair
  (implies (tree-listp (strip-cdrs-gen alst))
           (tree-listp (strip-cdrs-gen
                        (del-pair x alst)))))


(defthm tree-listp-through-sort
  (implies (and (tree-listp (strip-cdrs-gen alst))
                (greater-all len-tia tia)
                (not (member-gen nil (strip-cars-gen alst)))
                (alistp-gen alst)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index tia))
                (good-taxon-index-halist tia))
           (tree-listp (strip-cdrs-gen
                         (sort-the-alist-by-insertion
                          alst tia len-tia)))))


(defthm member-len-del-pair-one-less
  (implies (member-gen x (strip-cars-gen alst))
           (equal (len (del-pair x alst))
                  (1- (len (double-rewrite alst))))))

(defthm len-sort-by-insertion
  (implies (and (greater-all len-tia tia)
                (not (member-gen nil (strip-cars-gen alst)))
                (alistp-gen alst)
                (subset (strip-cars-gen alst)
                        (get-taxa-from-taxon-index tia))
                (good-taxon-index-halist tia))
           (equal (len (sort-the-alist-by-insertion
                        alst tia len-tia))
                  (len (double-rewrite alst)))))

(defthm len-cluster-sort
  (implies (and (good-taxon-index-halist tia)
                (taspip flg x)
                (subset (mytips x)
                        (get-taxa-from-taxon-index
                         tia))
                (rationalp len-tia)
                (greater-all len-tia tia))
           (equal (len (cluster-sort-by-insertion
                        flg x tia len-tia))
                  (len (double-rewrite x))))
  :hints (("Subgoal *1/3''" :expand
           (cluster-sort-by-insertion flg x tia len-tia)
          :in-theory
          (disable taspip-subset-strip-cars-mytips
                   subset-mytips-cluster-sort-by-insertion
                   keys-from-pair-key-subset-x
                   not-member-nil-mytips
                   not-member-nil-mytips-ans)
          :use ((:instance taspip-subset-strip-cars-mytips
                           (x (cluster-sort-by-insertion
                               nil x tia len-tia))
                           (flg nil))
                (:instance subset-mytips-cluster-sort-by-insertion
                           (flg nil))
                (:instance not-member-nil-mytips)))
))

(defthm tree-listp-through-cluster-sort
  (implies (and (tree-listp x)
                (taspip flg x)
                (consp x)
                (good-taxon-index-halist tia)
                (subset (mytips x)
                        (get-taxa-from-taxon-index
                         tia))
                (rationalp len-tia)
                (greater-all len-tia tia))
           (tree-listp (cluster-sort-by-insertion
                         flg x tia len-tia)))
  :hints (("Subgoal *1/27'5'"
           :cases ((consp x1)))
          ("Subgoal *1/27.1"
           :in-theory
           (disable len-greater-1-tree-listp=treep
                    )
           :use (:instance
                 len-greater-1-tree-listp=treep
                 (x (cluster-sort-by-insertion t x1 tia len-tia))))
          ("Subgoal *1/17'5'"
           :cases ((consp x1)))
          ("Subgoal *1/17.1"
           :in-theory
           (disable len-greater-1-tree-listp=treep
                    )
           :use (:instance
                 len-greater-1-tree-listp=treep
                 (x (cluster-sort-by-insertion t x1 tia len-tia))))
          ("Subgoal *1/2'" :expand (cluster-sort-by-insertion
                                    flg x tia len-tia))
          ("Subgoal *1/2.2''"
           :in-theory (disable member-of-tree-listp-is-treep)
           :use (:instance member-of-tree-listp-is-treep
                           (x (cdr
                              (hons-assoc-equal
                               (get-min-key
                                (pair-key-with-value (cluster-sort-by-insertion nil x tia len-tia))
                                nil len-tia tia)
                               (pair-key-with-value (cluster-sort-by-insertion nil x tia len-tia)))))
                           (lst (strip-cdrs-gen
                                 (pair-key-with-value (cluster-sort-by-insertion
                                                       nil x tia len-tia))
                                ))))
))

(defthm treep-cluster
  (implies (and (treep x)
                (taspip flg x)
                (good-taxon-index-halist taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index taxon-index-alist))
                (rationalp length-taxon-index-alist)
                (greater-all length-taxon-index-alist
                             taxon-index-alist))
           (treep
            (cluster-sort-by-insertion
             flg x taxon-index-alist
             length-taxon-index-alist)))
)


;; major properties of order-by-insertion
(defthm subset-mytips-through-order
  (implies (and (taspip flg x)
                (greater-all len-tia tia))
           (subset (mytips (order-by-insertion-help flg x tia len-tia))
                   (mytips x))))

(defthm taspip-through-order
  (implies (and (taspip flg x)
                (greater-all len-tia tia)
                (subset (mytips x)
                        (get-taxa-from-taxon-index tia))
                (good-taxon-index-halist tia))
           (taspip flg (order-by-insertion-help flg x tia len-tia))))

(defthm order-by-insertion-gives-orderedp
  (implies (and (taspip flg x)
                (good-taxon-index-halist
                 taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index
                         taxon-index-alist))
                (rationalp length-taxon-index-alist)
                (greater-all length-taxon-index-alist
                             taxon-index-alist))
           (orderedp flg
            (order-by-insertion-help flg x taxon-index-alist
                                length-taxon-index-alist)
            taxon-index-alist)))

(defthm order-by-insertion-gives-treep
  (implies (and (treep x)
                (taspip flg x)
                (good-taxon-index-halist taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index taxon-index-alist))
                (rationalp length-taxon-index-alist)
                (greater-all length-taxon-index-alist
                             taxon-index-alist))
           (treep (order-by-insertion-help flg x taxon-index-alist
                                      length-taxon-index-alist))))


(defthm order-by-insertion-gives-tree-listp
  (implies (and (tree-listp x)
                (taspip flg x)
                (good-taxon-index-halist taxon-index-alist)
                (subset (mytips x)
                        (get-taxa-from-taxon-index taxon-index-alist))
                (rationalp length-taxon-index-alist)
                (greater-all length-taxon-index-alist
                             taxon-index-alist))
           (tree-listp (order-by-insertion-help flg x taxon-index-alist
                                      length-taxon-index-alist))))

(in-theory (disable order-by-insertion-help))

;; and then for a list of trees
(defun order-each-by-insertion
  (input-trees taxon-index-alist length-taxon-index-alist)

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
;            mapping given.  Ordering is achieved using an insertion sort
;            algorithm. Consider also order-each-by-merge."
  (declare (xargs :guard (and (taspip nil input-trees)
                              (good-taxon-index-halist
                               taxon-index-alist)
                              (subset (mytips input-trees)
                                      (get-taxa-from-taxon-index
                                       taxon-index-alist))
                              (rationalp length-taxon-index-alist)
                              (greater-all length-taxon-index-alist
                                           taxon-index-alist))))
  (if (atom input-trees)
      nil
    (hons (order-by-insertion (car input-trees)
                              taxon-index-alist)
          (order-each-by-insertion (cdr input-trees)
                                   taxon-index-alist
                                   length-taxon-index-alist))))
