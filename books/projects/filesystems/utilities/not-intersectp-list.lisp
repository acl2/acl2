(in-package "ACL2")

;  not-intersectp-list.lisp                             Mihir Mehta

(include-book "../file-system-lemmas")
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

(defthm not-intersectp-list-when-subsetp-1
  (implies (and (not-intersectp-list y l)
                (subsetp-equal x y))
           (not-intersectp-list x l))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm not-intersectp-list-when-subsetp-2
  (implies (and (not-intersectp-list x l2)
                (subsetp-equal l1 l2))
           (not-intersectp-list x l1))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm not-intersectp-list-of-true-list-fix
  (equal (not-intersectp-list x (true-list-fix l))
         (not-intersectp-list x l))
  :hints (("Goal" :in-theory (enable not-intersectp-list))))

(defthm
  flatten-subset-no-duplicatesp-lemma-1
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

;; This is, sort of, the main lemma.
(defthm flatten-subset-no-duplicatesp
  (implies (and (subsetp-equal x y)
                (no-duplicatesp-equal (flatten y))
                (no-duplicatesp-equal x))
           (no-duplicatesp-equal (flatten x))))
