; Copyright (C) 2017, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(defthm make-character-list-makes-character-list
  (character-listp (make-character-list x)))

(defthm len-of-binary-append
  (equal (len (binary-append x y)) (+ (len x) (len y))))

(defthm len-of-make-character-list
  (equal (len (make-character-list x)) (len x)))

(defthm len-of-revappend
  (equal (len (revappend x y)) (+ (len x) (len y))))

(defthm len-of-first-n-ac
  (implies (natp i) (equal (len (first-n-ac i l ac)) (+ i (len ac)))))

(defthm nthcdr-of-binary-append-1
  (implies (and (integerp n) (>= n (len x)))
           (equal (nthcdr n (binary-append x y))
                  (nthcdr (- n (len x)) y)))
  :hints (("Goal" :induct (nthcdr n x)) ))

(defthm first-n-ac-of-binary-append-1
  (implies (and (natp i) (<= i (len x)))
           (equal (first-n-ac i (binary-append x y) ac)
                  (first-n-ac i x ac))))

(defthm by-slice-you-mean-the-whole-cake
  (implies (true-listp l)
           (equal (first-n-ac (len l) l ac)
                  (revappend ac l)))
  :hints (("Goal" :induct (revappend l ac)) )
  :rule-classes ((:rewrite :corollary
                           (implies (and (equal i (len l)) (true-listp l))
                                    (equal (first-n-ac i l ac) (revappend ac l)))) ))

(defthm assoc-after-delete-assoc
  (implies (not (equal name1 name2))
           (equal (assoc-equal name1 (delete-assoc name2 alist))
                  (assoc-equal name1 alist))))

(defthm character-listp-of-first-n-ac
  (implies (and (character-listp l) (character-listp acc) (<= n (len l)))
           (character-listp (first-n-ac n l acc))))

(defthm character-listp-of-nthcdr
  (implies (and (character-listp l))
           (character-listp (nthcdr n l))))

(defthm already-a-character-list
  (implies (character-listp x) (equal (make-character-list x) x)))

(defthm make-character-list-of-binary-append
  (equal (make-character-list (binary-append x y))
         (binary-append (make-character-list x) (make-character-list y))))

(defthm len-of-nthcdr-1 (<= (len (nthcdr n l)) (len l))
  :rule-classes :linear)

(defthm len-of-nthcdr-2
  (implies (and (consp l) (integerp n) (> n 0))
           (< (len (nthcdr n l)) (len l)))
  :rule-classes :linear)

(defthmd revappend-is-append-of-rev
  (equal (revappend x (binary-append y z))
         (binary-append (revappend x y) z)))

(defthm binary-append-take-nthcdr
  (implies (and (natp i) (<= i (len l)))
           (equal (binary-append (first-n-ac i l ac) (nthcdr i l))
                  (revappend ac l)))
  :hints (("Goal" :induct (first-n-ac i l ac))
          ("Subgoal *1/1'''"
           :use (:instance revappend-is-append-of-rev
                           (x ac) (y nil) (z l)))))

(defthm take-of-take
  (implies (and (natp m) (integerp n) (<= m n) (<= n (len l)))
           (equal (first-n-ac m (take n l) ac) (first-n-ac m l ac)))
  :hints (("Goal" :in-theory (disable binary-append-take-nthcdr)
           :use (:instance binary-append-take-nthcdr (ac nil) (i n))) ))

(defthm nth-of-binary-append-1
  (implies (and (integerp n) (>= n (len x)))
           (equal (nth n (binary-append x y))
                  (nth (- n (len x)) y)))
  :hints (("goal" :induct (nth n x))))

(defthm nth-of-binary-append-2
  (implies (and (natp n) (< n (len x)))
           (equal (nth n (binary-append x y))
                  (nth n x))))

(defthm binary-append-is-associative
  (equal (binary-append (binary-append a b) c)
         (binary-append a (binary-append b c))))

(defthm member-of-a-nat-list
  (implies (and (nat-listp lst)
                (member-equal x lst))
           (and (integerp x) (<= 0 x)))
  :rule-classes ((:rewrite :corollary (implies (and (nat-listp lst)
                                                   (member-equal x lst))
                                              (<= 0 x)))
                 (:forward-chaining :corollary (implies (and (member-equal x lst)
                                                             (nat-listp lst))
                                                        (integerp x)))))

(defthm non-nil-nth
  (implies (and (natp n) (nth n l))
           (< n (len l)))
  :rule-classes (:rewrite :linear))

(defthm update-nth-of-boolean-list
  (implies (and (boolean-listp l) (booleanp val))
           (boolean-listp (update-nth key val l))))

(defthm nat-listp-of-binary-append
  (implies (true-listp x)
           (equal (nat-listp (binary-append x y))
                  (and (nat-listp x) (nat-listp y)))))

(defthm eqlable-listp-if-nat-listp (implies (nat-listp l) (eqlable-listp l)))

(defthm member-of-binary-append
  (iff (member-equal x (binary-append lst1 lst2))
       (or (member-equal x lst1)
           (member-equal x lst2))))

(defthm no-duplicatesp-of-append
  (equal (no-duplicatesp-equal (binary-append x y))
         (and (no-duplicatesp x)
              (no-duplicatesp y)
              (not (intersectp-equal x y)))))

(defthm intersectp-of-append-1
  (equal (intersectp-equal z (binary-append x y))
         (or (intersectp-equal z x)
             (intersectp-equal z y))))

(defthm intersectp-of-append-2
  (equal (intersectp-equal (binary-append x y) z)
         (or (intersectp-equal x z)
             (intersectp-equal y z))))

(defthm intersectp-is-commutative
  (equal (intersectp-equal x y)
         (intersectp-equal y x)))

(defthm subsetp-of-binary-append-1
  (subsetp-equal y (binary-append x y)))

(defthm subsetp-of-binary-append-2
  (subsetp-equal x (binary-append x y)))

(defthm subsetp-of-binary-append-3
  (equal (subsetp-equal (binary-append x y) z)
         (and (subsetp-equal x z) (subsetp-equal y z))))

(defthm subsetp-is-transitive
  (implies (and (subsetp-equal x y) (subsetp-equal y z))
           (subsetp-equal x z)))

(defthm member-of-subset
  (implies (and (subsetp-equal lst1 lst2)
                (member-equal x lst1))
           (member-equal x lst2)))

(defthm nth-of-revappend
  (implies (and (natp n))
           (equal (nth n (revappend x y))
                  (if (< n (len x))
                      (nth (- (len x) (+ n 1)) x)
                      (nth (- n (len x)) y)))))

(defthm true-listp-of-make-list-ac
  (implies (true-listp ac)
           (true-listp (make-list-ac n val ac))))

(defthm len-of-make-list-ac
  (implies (and (integerp n) (>= n 0))
           (equal (len (make-list-ac n val ac))
                  (+ n (len ac)))))

(defthm boolean-listp-of-make-list-ac
  (implies (booleanp val)
           (equal (boolean-listp (make-list-ac n val ac))
                  (boolean-listp ac))))

(defthm booleanp-of-car-make-list
  (implies (and (booleanp val)
                (boolean-listp ac)
                (> (+ n (len ac)) 0))
           (booleanp (car (make-list-ac n val ac)))))

(defthm car-of-make-list
  (equal (car (make-list-ac n val ac))
         (if (zp n) (car ac) val)))

(defthm cdr-of-make-list
  (equal (cdr (make-list-ac n val ac))
         (if (zp n)
             (cdr ac)
             (make-list-ac (- n 1) val ac))))
