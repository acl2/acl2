(in-package "PROOF")
; (include-book "sets")

(defun good-order-list (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (integerp (cdar x))
           (or (integerp (caar x))
               (and (symbolp (caar x))
                    (not (equal (caar x) nil))))
           (good-order-list (cdr x)))
    (equal x nil)))

(defun get-taxa-from-order (x)
  (declare (xargs :guard (good-order-list x)))
  (if (consp x)
      (cons (caar x) (get-taxa-from-order (cdr x)))
    nil))

;; generally helpful thms with a good-order
(defthm not-member-ints-not-equal
  (implies (and (good-order-list order)
                (not (member-equal x (strip-cdrs order)))
                (member-equal y (get-taxa-from-order order)))
           (not (equal x
                       (cdr (assoc-equal y order))))))

(defthm not-equal-members-not-equal-vals
  (implies (and (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (member-equal x (get-taxa-from-order order))
                (member-equal y (get-taxa-from-order order))
                (not (equal x y)))
           (not (equal (cdr (assoc-equal x order))
                       (cdr (assoc-equal y order))))))

(defthm good-order-member-integer-cdr
  (implies (and (good-order-list order)
                (member-equal f (get-taxa-from-order order)))
           (integerp (cdr (assoc-equal f order))))
  :rule-classes :forward-chaining)

(defthm member-taxa-assoc-equal
  (implies (and (good-order-list order)
                (member-equal x (get-taxa-from-order order)))
           (assoc-equal x order)))

(defthm member-taxa-not-consp
  (implies (and (good-order-list order)
                (member-equal x (get-taxa-from-order order)))
           (not (consp x))))

(defthm good-order-list-alistp
  (implies (good-order-list order)
           (alistp order)))

(defthm not-assoc-nil
  (implies (good-order-list order)
           (not (assoc-equal nil order))))

;; omerge
(defun olessp (x y order)
  (declare (xargs :guard (and (good-order-list order)
                              (member-equal
                               x
                               (get-taxa-from-order order))
                              (member-equal
                               y
                               (get-taxa-from-order order)))))
  (if (< (cdr (assoc-equal x order))
         (cdr (assoc-equal y order)))
      t
    nil))

(defun omerge (x y order)
  (declare (xargs :measure (+ (acl2-count x)
                              (acl2-count y))
                  :guard (and (good-order-list order)
                              (subset
                               x
                               (get-taxa-from-order order))
                              (subset
                               y
                               (get-taxa-from-order order)))))
  (cond ((not (consp x)) y)
        ((not (consp y)) x)
        ((olessp (car x) (car y) order)
         (cons (car x) (omerge (cdr x) y order)))
        ((olessp (car y) (car x) order)
         (cons (car y) (omerge x (cdr y) order)))
        (t (cons (car x) (omerge (cdr x) (cdr y) order)))))


(defun mytips (tree)
  (declare (xargs :guard t))
  (if (consp tree)
      (append (mytips (car tree))
              (mytips (cdr tree)))
    (if (equal tree nil)
        nil
      (list tree))))

(defun smaller-all (x list order)
  (declare (xargs :guard (and (good-order-list order)
                              (member-equal
                               x
                               (get-taxa-from-order order))
                              (subset
                               list
                               (get-taxa-from-order order)))))

  (if (consp list)
      (and (< (cdr (assoc-equal x order))
              (cdr (assoc-equal (car list) order)))
           (smaller-all x (cdr list) order))
    t))

(defun smaller-all-list (list1 list2 order)
  (declare (xargs :measure (+ (acl2-count list1)
                              (acl2-count list2))
                  :guard (and (good-order-list order)
                              (subset
                               list1
                               (get-taxa-from-order order))
                              (subset
                               list2
                               (get-taxa-from-order order)))))
  (if (consp list1)
      (and (smaller-all (car list1) list2 order)
           (smaller-all-list (cdr list1) list2 order))
    t))


;; true-listp
(defthm true-listp-append
  (equal (true-listp (append x y))
         (true-listp y)))

(defthm true-listp-cdr
  (implies (true-listp x)
           (true-listp (cdr x))))

(defthm true-listp-mytips
  (true-listp (mytips x)))

(defthm true-listp-omerge
  (implies (and (true-listp x)
                (true-listp y))
           (true-listp (omerge x y order))))

(defthm append-nil
  (implies (true-listp x)
           (equal (append x nil)
                  x)))

;; smaller-all
(defthm smaller-member-smaller
  (implies (and (member-equal x y)
                (smaller-all z y order))
           (< (cdr (assoc-equal z order))
              (cdr (assoc-equal x order)))))

(defthm smaller-subset-smaller
  (implies (and (subset x y)
                (smaller-all z y order))
           (smaller-all z x order)))

(defthm smaller-all-append
  (implies (and (smaller-all x y order)
                (smaller-all x z order))
           (smaller-all x (append y z) order)))

(defthm smaller-all-difference
  (implies (smaller-all x y order)
           (smaller-all x (difference y z) order)))

(in-theory (disable smaller-all))

;; omerge

(defthm member-gives-omerge-1
  (implies (member-equal x y)
           (member-equal x (omerge y z order))))

(defthm subset-gives-omerge-1
  (implies (subset x y)
           (subset x (omerge y z order))))

(defthm member-gives-omerge-2
  (implies (and (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (subset y
                        (get-taxa-from-order order))
                (subset z
                        (get-taxa-from-order order))
                (member-equal x y))
           (member-equal x (omerge z y order))))

(defthm subset-gives-omerge-2
  (implies (and (subset x y)
                (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (subset y
                        (get-taxa-from-order order))
                (subset z (get-taxa-from-order order)))
           (subset x (omerge z y order))))

(defthm subset-omerge-append
  (implies (and (subset x y)
                (subset u v))
           (subset (omerge x u order)
                   (append y v))))

(defthm subset-omerge-cons
  (implies (subset y z)
           (subset (omerge (list x) y order)
                   (cons x z))))

(defthm subset-list-gives-omerge-1
  (implies (subset-list x y)
           (subset-list x (omerge y z order))))

(defthm subset-list-gives-omerge-2
  (implies (and (subset-list x y)
                (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (subset y (get-taxa-from-order order))
                (subset z (get-taxa-from-order order)))
           (subset-list x (omerge z y order))))

(defthm subset-list-append-omerge
  (implies (and (subset-list x y)
                (subset-list u v)
                (good-order-list order)
                (no-duplicatesp-equal (strip-cdrs order))
                (subset y (get-taxa-from-order order))
                (subset v (get-taxa-from-order order)))
           (subset-list (append x u)
                        (omerge y v order))))

(defthmd smaller-all-omerge-becomes-cons
  (implies (and (member-equal x1 (get-taxa-from-order order))
                (good-order-list order)
                (smaller-all x1 y order)
                (subset y (get-taxa-from-order order)))
           (equal (omerge (list x1) y order)
                  (cons x1 y)))
  :hints (("Goal" :in-theory (enable smaller-all))))

(defthm difference-omerge
  (implies (and (not (intersect x y))
                (true-listp x)
                (subset x (get-taxa-from-order order))
                (subset y (get-taxa-from-order order))
                (no-duplicatesp-equal (strip-cdrs order))
                (no-duplicatesp-equal x)
                (no-duplicatesp-equal y)
                (good-order-list order))
           (equal (difference (omerge x y order)
                              x)
                  y))
  :hints (("Goal" :induct (omerge x y order))
          ("Subgoal *1/3'4'" :in-theory
           (disable difference-not-member)
           :use (:instance difference-not-member
                           (x x1)
                           (y (omerge x2 y order))
                           (z y)))
          ("Subgoal *1/3.2" :in-theory
           (disable subset-omerge-append
                    not-member-subset)
           :use (:instance subset-omerge-append
                           (x x2)
                           (y x2)
                           (u y)
                           (v y)))
          ("Subgoal *1/3.2''" :use
           (:instance not-member-subset
                      (x x1) (y (append x2 y))
                      (z (omerge x2 y order))))
          ("Subgoal *1/3.1" :in-theory
           (disable subset-omerge-append
                    not-member-subset)
           :use (:instance subset-omerge-append
                           (x x2)
                           (y x2)
                           (u y)
                           (v y)))
          ("Subgoal *1/3.1''" :use
           (:instance not-member-subset
                      (x x1) (y (append x2 y))
                      (z (omerge x2 y order))))
          ("Subgoal *1/3.1'4'"
           :use (:instance difference-not-member
                           (x x1)
                           (y (omerge x2 y order))
                           (z x2)))
))

(defthm needs-to-be-in-one
  (implies (member-equal y1 (append x y2))
           (or (member-equal y1 x)
               (member-equal y1 y2)))
  :rule-classes nil)

(defthm not-intersect-no-dups-no-dups-omerge
  (implies (and (not (intersect x y))
                (no-duplicatesp-equal x)
                (no-duplicatesp-equal y)
                (true-listp x)
                (true-listp y)
                (no-duplicatesp-equal (strip-cdrs order))
                (good-order-list order)
                (subset x (get-taxa-from-order order))
                (subset y (get-taxa-from-order order)))
           (no-duplicatesp-equal (omerge x y order)))
  :hints (("Goal" :induct (omerge x y order))
          ("Subgoal *1/4'6'" :in-theory
           (disable subset-omerge-append
                    binary-append
                    subset-same-members
                    not-member-subset)
           :use (:instance subset-omerge-append
                           (x (cons x1 x2))
                           (y (cons x1 x2))
                           (u y2)
                           (v y2)))
          ("Subgoal *1/4'8'" :use
           (:instance not-member-subset
                      (x y1) (y (append (cons x1 x2) y2))
                      (z (omerge (cons x1 x2) y2 order))))
          ("Subgoal *1/4'10'" :use
           (:instance needs-to-be-in-one
                      (x (cons x1 x2))))
          ("Subgoal *1/3'4'" :in-theory
           (disable subset-omerge-append
                    not-member-subset)
           :use (:instance subset-omerge-append
                           (x x2)
                           (y x2)
                           (u y)
                           (v y)))
          ("Subgoal *1/3'6'" :use
           (:instance not-member-subset
                      (x x1)
                      (y (append x2 y))
                      (z (omerge x2 y order))))
))
