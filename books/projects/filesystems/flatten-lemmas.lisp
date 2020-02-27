(in-package "ACL2")

(local (include-book "file-system-lemmas"))
(include-book "std/lists/flatten" :dir :system)

(defthm no-duplicatesp-of-member
  (implies (and (not (no-duplicatesp x))
                (no-duplicatesp (flatten lst)))
           (not (member-equal x lst))))

(defund not-intersectp-list (x l)
  (declare (xargs :guard (and (true-listp x) (true-list-listp l))))
  (or (atom l)
      (and (not (intersectp-equal x (car l)))
           (not-intersectp-list x (cdr l)))))

(defcong list-equiv equal (not-intersectp-list x l) 1
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm not-intersectp-list-correctness-1
  (equal (intersectp-equal x (flatten l))
         (not (not-intersectp-list x l)))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthmd not-intersectp-list-correctness-2
  (implies (and (not-intersectp-list x l)
                (member-equal y l))
           (not (intersectp-equal x y)))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm not-intersectp-list-of-append-1
  (equal (not-intersectp-list x (binary-append l1 l2))
         (and (not-intersectp-list x l1)
              (not-intersectp-list x l2)))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm not-intersectp-list-when-atom
  (implies (atom x) (not-intersectp-list x l))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm not-intersectp-equal-if-subset
  (implies (and (not-intersectp-list x l2)
                (subsetp-equal l1 l2))
           (not-intersectp-list x l1))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm not-intersectp-list-of-true-list-fix
  (equal (not-intersectp-list x (true-list-fix l))
         (not-intersectp-list x l))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthmd flatten-subset-no-duplicatesp-lemma-1
  (implies (and (consp z)
                (no-duplicatesp (flatten z))
                (member-equal y z)
                (not (equal y (car z))))
           (not (intersectp-equal (car z) y)))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm
  flatten-subset-no-duplicatesp-lemma-2
  (implies (and (no-duplicatesp (flatten z))
                (consp z)
                (member-equal x z)
                (member-equal y z)
                (not (equal y x)))
           (not (intersectp-equal x y)))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(local
 (defthm flatten-subset-no-duplicatesp-lemma-3
   (implies (and (member-equal z y)
                 (not (member-equal z x))
                 (subsetp-equal x y)
                 (no-duplicatesp-equal (flatten y)))
            (not-intersectp-list z x))
   :hints (("Goal" :in-theory (enable not-intersectp-list)))))

;; This is sort of the main lemma
(defthm flatten-subset-no-duplicatesp
  (implies (and (subsetp-equal x y)
                (no-duplicatesp-equal (flatten y))
                (no-duplicatesp-equal x))
           (no-duplicatesp-equal (flatten x))))

(defun disjoint-list-listp (x)
  (if (atom x)
      (equal x nil)
    (and (not-intersectp-list (car x) (cdr x))
         (disjoint-list-listp (cdr x)))))

(defun no-duplicates-listp (x)
  (if (atom x)
      (equal x nil)
    (and (no-duplicatesp (car x)) (no-duplicates-listp (cdr x)))))

(defthm flatten-disjoint-lists
  (implies (true-listp l)
           (equal (no-duplicatesp-equal (flatten l))
                  (and (disjoint-list-listp l) (no-duplicates-listp l)))))

;; This theorem won't go through because both
;; (disjoint-list-listp '((1 2) (3 4))) and
;; (subsetp-equal '((1 2) (1 2)) '((1 2) (3 4))) are t.
;; (verify (implies (and (subsetp-equal x y) (disjoint-list-listp y)) (disjoint-list-listp x)))

(defun member-intersectp-equal (x y)
  (declare (xargs :guard (and (true-list-listp x) (true-list-listp y))))
  (and (consp x)
       (or (not (not-intersectp-list (car x) y))
           (member-intersectp-equal (cdr x) y))))

(defcong list-equiv
  equal (member-intersectp-equal x y)
  1
  :hints (("goal" :in-theory (enable fast-list-equiv)
           :induct (fast-list-equiv x x-equiv))))

(defthm when-append-is-disjoint-list-listp
  (equal (disjoint-list-listp (binary-append x y))
         (and (disjoint-list-listp (true-list-fix x))
              (disjoint-list-listp y)
              (not (member-intersectp-equal x y)))))

(defthm member-intersectp-with-subset
  (implies (and (member-intersectp-equal z x)
                (subsetp-equal x y))
           (member-intersectp-equal z y)))

(defthm
  intersectp-member-when-not-member-intersectp
  (implies (and (member-equal x lst2)
                (not (member-intersectp-equal lst1 lst2)))
           (not-intersectp-list x lst1))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(local
 (defthm member-intersectp-binary-append-lemma
   (equal (member-intersectp-equal e (binary-append x y))
          (or (member-intersectp-equal e x)
              (member-intersectp-equal e y)))))

(local
 (defthm member-intersectp-is-commutative-lemma-1
   (implies (not (consp x))
            (not (member-intersectp-equal y x)))
   :hints (("Goal" :in-theory (enable not-intersectp-list)))))

(defthm member-intersectp-is-commutative-lemma-2
  (implies (and (consp x)
                (not (not-intersectp-list (car x) y)))
           (member-intersectp-equal y x))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthmd member-intersectp-is-commutative-lemma-3
  (implies (and (consp x)
                (not-intersectp-list (car x) y))
           (equal (member-intersectp-equal y (cdr x))
                  (member-intersectp-equal y x)))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm member-intersectp-is-commutative
  (equal (member-intersectp-equal x y)
         (member-intersectp-equal y x))
  :hints (("Goal" :in-theory (enable member-intersectp-is-commutative-lemma-3)) ))

(defthm
  another-lemma-about-member-intersectp
  (implies (or (member-intersectp-equal x z)
               (member-intersectp-equal y z))
           (member-intersectp-equal z (binary-append x y))))

(defthm not-intersectp-list-of-append-2
  (equal (not-intersectp-list (binary-append x y) l)
         (and (not-intersectp-list x l)
              (not-intersectp-list y l)))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm no-duplicates-listp-of-append
  (equal (no-duplicates-listp (binary-append x y))
         (and (no-duplicates-listp (true-list-fix x))
              (no-duplicates-listp y))))

(defthm member-intersectp-binary-append
  (equal (member-intersectp-equal e (binary-append x y))
         (or (member-intersectp-equal e x)
             (member-intersectp-equal e y)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (equal (member-intersectp-equal (binary-append x y) e)
           (or (member-intersectp-equal x e)
               (member-intersectp-equal y e))))))

(defthm not-intersectp-list-of-flatten
  (equal (not-intersectp-list (flatten x) y)
         (not (member-intersectp-equal x y))))
