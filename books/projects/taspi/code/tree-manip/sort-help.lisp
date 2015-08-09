;; some basic functions helpful for various forms of sort

;; should get-min and greater all be back in insertion??

(in-package "ACL2")
(include-book "../gen-trees/sets-lists-trees")
; cert_param: (non-acl2r)

;; Pairs first-taxon with rest of term it appears in
(defun pair-key-with-value (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (cons (hons (first-taxon (car lst))
                (car lst))
           (pair-key-with-value (cdr lst)))))

(defthm pair-key-with-value-when-not-consp
  (implies (not (consp lst))
           (equal (pair-key-with-value lst)
                  nil)))

(defthm pair-key-with-value-of-consp
  (equal (pair-key-with-value (cons first rest))
         (cons (cons (first-taxon first) first)
               (pair-key-with-value rest))))

(dis+ind pair-key-with-value)

(defthm alistp-gen-pair-key-with-value
  (alistp-gen (pair-key-with-value x)))

(defthm keys-from-pair-key-subset-x
  (implies (taspip nil x)
           (subset (strip-cars-gen (pair-key-with-value x))
                   (mytips x))))

(defthm taspip-strip-cars-pair
  (implies (taspip flg x)
           (not (member-gen nil (strip-cars-gen
                                 (pair-key-with-value
                                  x))))))

(defthm taspip-subset-strip-cars-mytips
  (implies (taspip flg x)
           (subset (strip-cars-gen (pair-key-with-value
                                    x))
                   (mytips x))))

(defthm taspip-nil-gives-taspip-nil-strip-cdrs
  (implies (taspip nil x)
           (taspip nil (strip-cdrs-gen
                        (pair-key-with-value x)))))

(defthm consp-gives-consp-pair-key
  (implies (consp x)
           (consp (pair-key-with-value x))))

(defthm subset-mytips-strip-cdrs-pair
  (subset (mytips (strip-cdrs-gen (pair-key-with-value x)))
          (mytips x)))

(defun ordered-list (list order)
  (declare (xargs :guard (and (good-taxon-index-halist order)
                              (subset list
                                      (get-taxa-from-taxon-index
                                       order)))))
  (if (consp list)
      (if (consp (cdr list))
          (and (<= (cdr (assoc-hqual (car list) order))
                   (cdr (assoc-hqual (cadr list) order)))
               (ordered-list (cdr list) order))
        t)
    t))


(defun get-firsts (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (first-taxon (car x))
            (get-firsts (cdr x)))
    x))

(defthm subset-get-firsts-mytips
  (implies (taspip flg x)
           (subset (get-firsts x)
                   (mytips x))))

(defun orderedp (flg x order)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;   Determines if the tree given is ordered according to the order given.~/
;   ~/
;   Arguments:
;      (1) flg - nil indicates a set of trees, non-nil indicates a single tree
;      (2) x - a tree
;      (3) order - a mapping from taxa names to integers

;   Details: Taxa names in order must match those in the tree.  Branch lengths
;            may or may not be present. "
  (declare (xargs :guard (and (good-taxon-index-halist order)
                              (subset (mytips x)
                                      (get-taxa-from-taxon-index
                                       order))
                              (taspip flg x))
                  :guard-hints (("Subgoal 4" :in-theory
                                 (disable subset-get-firsts-mytips)
                                 :use (:instance subset-get-firsts-mytips)))
                  :measure (make-ord (1+ (acl2-count x))
                                     1
                                     (if flg 1 0))))
  (if (consp x)
      (if flg
          (and (ordered-list (get-firsts x) order)
               (orderedp nil x order))
        (and (orderedp t (car x) order)
             (orderedp nil (cdr x) order)))
    t))


(defthm assoc-hqual-from-member-gen-strip-cars
  (implies (and (alistp-gen alst)
                (member-gen x (strip-cars-gen alst)))
           (assoc-hqual x alst)))

(defthm ordered-nil-through-pair
  (implies (orderedp nil x tia)
           (orderedp nil (strip-cdrs-gen
                          (pair-key-with-value x))
                     tia)))

(defthm ordered-nil-gives-ordered-t-element
  (implies (and (member-gen x (strip-cars-gen alst))
                (orderedp nil (strip-cdrs-gen alst) tia))
           (orderedp t (cdr (assoc-hqual x alst)) tia)))


(defthm ordered-nil-through-del-pair
  (implies (orderedp nil (strip-cdrs-gen alst) tia)
           (orderedp nil (strip-cdrs-gen
                          (del-pair x alst)) tia)))

(defun valid-pairing (alst)
  (declare (xargs :guard (alistp-gen alst)))
  (if (consp alst)
      (and (equal (caar alst)
                  (first-taxon (cdar alst)))
           (valid-pairing (cdr alst)))
    t))

(defthm valid-pairing-pair-key
  (valid-pairing (pair-key-with-value x)))


(defthm valid-pair-first-taxon-cdr-assoc-equals-same
  (implies (and (valid-pairing alst)
                (consp alst)
                (member-gen x (strip-cars-gen alst)))
           (equal (first-taxon (cdr (assoc-hqual x alst)))
                  x)))

(defthm valid-pairing-through-del-pair
  (implies (valid-pairing alst)
           (valid-pairing (del-pair x alst))))

(defthm get-firsts-of-strip-cdrs-of-valid-pair-equal-strip-cars
  (implies (valid-pairing alst)
           (equal (get-firsts
                   (strip-cdrs-gen alst))
                  (strip-cars-gen alst))))

(defthm equal-car-assoc-key
  (implies (member-gen x (strip-cars-gen alst))
           (equal (car (assoc-hqual x alst))
                  x)))

(defthm no-dups-gen-through-del-pair
  (implies (no-dups-gen (strip-cars-gen x))
           (no-dups-gen (strip-cars-gen (del-pair y x)))))

(defthm member-gen-car-strip-cars
  (implies (and (consp x)
                (alistp-gen x)
                (subset (strip-cars-gen x) y))
           (member-gen (car (strip-cars-gen x)) y)))

(defthm subset-strip-cars-through-evens
  (implies (subset (strip-cars-gen x) y)
           (subset (strip-cars-gen (evens-gen x)) y)))

(defthm alistp-gen-through-evens
  (implies (alistp-gen x)
           (alistp-gen (evens-gen x)))
  :hints (("Goal" :induct (evens-gen x))))

(defthm subset-strip-cars-pair-gives-member-gen-first-taxon
  (implies (and (consp x)
                (subset (strip-cars-gen
                         (pair-key-with-value x)) y))
           (member-gen (first-taxon x) y))
  :hints (("Goal" :induct (first-taxon x))))

(defthm consp-through-strip-cdrs
  (implies (consp x)
           (consp (strip-cdrs-gen x))))

(defthm taspi-t-subset-mytips-gives-member-gen-first
  (implies (and (taspip t x)
                (subset (mytips x) y))
           (member-gen (first-taxon x) y)))

(defthm subset-mytips-gives-subset-strip-cars-pair
  (implies (and (taspip flg x)
                (subset (mytips x) y))
           (subset (strip-cars-gen
                    (pair-key-with-value x)) y)))

(defthm consp-through-evens-gen
  (implies (consp x)
           (consp (evens-gen x))))


(defthm taspip-nil-through-strip-cdrs-evens
  (implies (taspip nil (strip-cdrs-gen x))
           (taspip nil (strip-cdrs-gen (evens-gen x)))))

(defthm taspip-flg-through-strip-cdrs-evens
  (implies (taspip flg (strip-cdrs-gen x))
           (taspip flg (strip-cdrs-gen (evens-gen x)))))

(defthm subset-mytips-evens-gen-mytips
  (subset (mytips (evens-gen x))
          (mytips x)))

(defthm subset-mytips-gives-subset-cdr
  (implies (subset (mytips x) y)
           (subset (mytips (cdr x)) y)))

(defthm subset-mytips-gives-subset-pair
  (implies (and (taspip flg x)
                (subset (mytips x) y))
           (subset (mytips (pair-key-with-value x)) y)))

(defthm orderedp-nil-through-evens
  (implies (orderedp nil (strip-cdrs-gen x) tia)
           (orderedp nil (strip-cdrs-gen (evens-gen x)) tia)))

(defthm valid-pairing-cdr
  (implies (valid-pairing x)
           (valid-pairing (cdr x))))

(defthm valid-pairing-through-evens-gen
  (implies (valid-pairing x)
           (valid-pairing (evens-gen x)))
  :hints (("Goal" :induct (evens-gen x))))

(defthm car-strip-cars-gen
  (implies (and (alistp-gen x)
                (consp x))
           (equal (car (strip-cars-gen x))
                  (caar x))))


(defthm member-of-tree-listp-is-treep
  (implies (and (tree-listp lst)
                (member-gen x (double-rewrite lst)))
           (treep x)))

(defthm member-gen-in-cars-member-gen-cdr-in-cdrs
  (implies (and (alistp-gen alst)
                (member-gen x (strip-cars-gen alst)))
           (member-gen (cdr
                        (assoc-hqual x alst))
                       (strip-cdrs-gen alst))))

(defthm len-greater-1-tree-listp=treep
  (implies (<= 2 (len (double-rewrite x)))
           (equal (treep x)
                  (tree-listp x))))

(defthm len-pair-key
  (equal (len (pair-key-with-value x))
         (len (double-rewrite x))))

(defthm len-strip-cdrs
  (implies (alistp-gen alst)
           (equal (len (strip-cdrs-gen alst))
                  (len (double-rewrite alst)))))

(defthm treep-and-consp-len-at-least-2
  (implies (and (treep x)
                (consp x))
           (<= 2 (len x))))

(defthm treep-and-not-tree-listp
  (implies (and (treep x)
                (not (tree-listp x)))
           (not (consp x)))
  :rule-classes :forward-chaining)

(defthm treep-through-pair-key
  (implies (tree-listp x)
           (tree-listp (strip-cdrs-gen (pair-key-with-value x)))))
