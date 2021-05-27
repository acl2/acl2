(in-package "ACL2")

(include-book "member-intersectp")
(include-book "std/lists/sets" :dir :system)
(include-book "centaur/fty/top" :dir :system)

;  flatten-equiv.lisp                                   Mihir Mehta

(defcong
  set-equiv
  equal (not-intersectp-list x l)
  2
  :hints
  (("goal"
    :in-theory
    (e/d nil
         ((:rewrite not-intersectp-list-when-subsetp-2)))
    :use
    ((:instance (:rewrite not-intersectp-list-when-subsetp-2)
                (l1 l)
                (x x)
                (l2 l-equiv))
     (:instance (:rewrite not-intersectp-list-when-subsetp-2)
                (l2 l)
                (x x)
                (l1 l-equiv))))))

(defund flatten-equiv (x y)
  (set-equiv (remove-equal nil (true-list-list-fix x))
             (remove-equal nil (true-list-list-fix y))))

(defequiv flatten-equiv
  :hints (("goal" :in-theory (enable flatten-equiv))))

(defthmd
  flatten-equiv-implies-equal-not-intersectp-list-2-lemma-1
  (equal (not-intersectp-list x
                              (remove-equal nil (true-list-list-fix l)))
         (not-intersectp-list x l))
  :hints (("goal" :in-theory (enable not-intersectp-list
                                     true-list-list-fix intersectp-equal))))

(defcong
  flatten-equiv
  equal (not-intersectp-list x l)
  2
  :hints
  (("goal"
    :in-theory (enable flatten-equiv)
    :use
    ((:instance
      flatten-equiv-implies-equal-not-intersectp-list-2-lemma-1
      (l l-equiv))
     flatten-equiv-implies-equal-not-intersectp-list-2-lemma-1))))

(defthmd
  flatten-equiv-implies-equal-member-intersectp-equal-1-lemma-1
  (equal (member-intersectp-equal (remove-equal nil (true-list-list-fix x))
                                  y)
         (member-intersectp-equal x y))
  :hints (("goal" :in-theory (enable not-intersectp-list
                                     true-list-list-fix intersectp-equal))))

(defcong
  set-equiv
  equal (member-intersectp-equal x y)
  1
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (set-equiv)
                    (member-intersectp-with-subset))
    :use ((:instance member-intersectp-with-subset (z y)
                     (x x)
                     (y x-equiv))
          (:instance member-intersectp-with-subset (z y)
                     (x x-equiv)
                     (y x))))))

(defcong
  set-equiv
  equal (member-intersectp-equal y x)
  2
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (set-equiv)
                    (member-intersectp-with-subset))
    :use ((:instance member-intersectp-with-subset (z y)
                     (x x)
                     (y x-equiv))
          (:instance member-intersectp-with-subset (z y)
                     (x x-equiv)
                     (y x))))))

(defcong
  flatten-equiv
  equal (member-intersectp-equal x y)
  1
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable member-intersectp-equal flatten-equiv)
    :use ((:instance
           flatten-equiv-implies-equal-member-intersectp-equal-1-lemma-1
           (x x-equiv))
          flatten-equiv-implies-equal-member-intersectp-equal-1-lemma-1))))

(defcong
  flatten-equiv
  equal (member-intersectp-equal y x)
  2
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable member-intersectp-equal flatten-equiv)
    :use ((:instance
           flatten-equiv-implies-equal-member-intersectp-equal-1-lemma-1
           (x x-equiv))
          flatten-equiv-implies-equal-member-intersectp-equal-1-lemma-1))))

(defthmd set-equiv-implies-equal-true-list-listp-of-list-fix-1-lemma-1
  (implies (and (not (true-list-listp x))
                (true-list-listp y)
                (true-listp x))
           (not (subsetp-equal x y)))
  :hints (("goal" :in-theory (enable subsetp-equal true-list-listp))))

(defthm
  set-equiv-implies-equal-true-list-listp-of-list-fix-1
  (implies (set-equiv x y)
           (equal (true-list-listp (true-list-fix x))
                  (true-list-listp (true-list-fix y))))
  :rule-classes :congruence
  :hints
  (("goal"
    :in-theory (enable set-equiv)
    :use
    ((:instance
      set-equiv-implies-equal-true-list-listp-of-list-fix-1-lemma-1
      (x (true-list-fix x))
      (y (true-list-fix y)))
     (:instance
      set-equiv-implies-equal-true-list-listp-of-list-fix-1-lemma-1
      (y (true-list-fix x))
      (x (true-list-fix y)))))))

(defthm commutativity-2-of-cons-under-flatten-equiv-lemma-1
  (set-equiv (list* x y z) (list* y x z))
  :hints (("goal" :in-theory (enable set-equiv))))

(defthm commutativity-2-of-cons-under-flatten-equiv
  (flatten-equiv (list* x y z)
                 (list* y x z))
  :hints (("goal" :in-theory (enable flatten-equiv))))

(defcong flatten-equiv flatten-equiv (append x y) 2
  :hints (("goal" :in-theory (e/d (flatten-equiv)
                                  ()))))

(defthm flatten-equiv-of-remove-of-nil
  (flatten-equiv (remove-equal nil x) x)
  :hints (("goal" :in-theory (e/d (flatten-equiv)
                                  ()))))

(defthm flatten-equiv-of-cons-when-atom
  (implies (atom x)
           (flatten-equiv (cons x y) y))
  :hints (("goal" :in-theory (e/d (flatten-equiv)
                                  ()))))

(defcong flatten-equiv flatten-equiv (cons x y) 2
  :hints (("goal" :in-theory (e/d (flatten-equiv)
                                  ()))))

(defthmd cons-equal-under-set-equiv-1
  (iff (set-equiv (cons x y1) (cons x y2))
       (set-equiv (remove-equal x y1)
                  (remove-equal x y2)))
  :instructions ((:= (cons x y2)
                     (cons x (remove-equal x y2))
                     :equiv set-equiv)
                 (:= (cons x y1)
                     (cons x (remove-equal x y1))
                     :equiv set-equiv)
                 (:dive 1)
                 :x (:dive 1)
                 (:= (subsetp-equal (remove-equal x y1)
                                    (remove-equal x y2)))
                 :top
                 (:= (subsetp-equal (remove-equal x y2)
                                    (cons x (remove-equal x y1)))
                     (subsetp-equal (remove-equal x y2)
                                    (remove-equal x y1)))
                 (:dive 2)
                 :x
                 :top :bash))

(defthm flatten-equiv-of-append-of-cons-1
  (flatten-equiv (append x (cons y z))
                 (cons y (append x z)))
  :hints (("goal" :in-theory (e/d (flatten-equiv)
                                  ()))))
