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

;; The following is redundant with the definition in
;; books/std/lists/nthcdr.lisp, from where it was taken with thanks to Jared
;; Davis.
(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (nfix (- (len l) (nfix n))))
  :hints (("Goal" :induct (nthcdr n l))))

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

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nth.lisp, from where it was taken with thanks.
(defthm nth-of-revappend
  (equal (nth n (revappend x y))
         (if (< (nfix n) (len x))
             (nth (- (len x) (+ 1 (nfix n))) x)
           (nth (- n (len x)) y))))

;; The following is redundant with the eponymous theorem in
;; books/misc/gentle.lisp, from where it was taken with thanks to
;; Messrs. Boyer, Hunt and Davis.
(defthm true-listp-of-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (true-listp ac)
                           (true-listp (make-list-ac n val ac))))))

;; The following is redundant with the eponymous theorem in
;; books/centaur/ubdds/param.lisp, from where it was taken with thanks to
;; Messrs. Boyer and Hunt.
(defthm len-of-make-list-ac
  (equal (len (make-list-ac n val acc))
         (+ (nfix n) (len acc))))

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

(defthm member-equal-of-nth
  (implies (and (natp n) (< n (len l)))
           (member-equal (nth n l) l)))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm
    logand-ash-lemma-1
    (implies (and (natp c))
             (unsigned-byte-p c (logand i (- (ash 1 c) 1)))))
  )

(defthm make-character-list-of-revappend
  (equal (make-character-list (revappend x y))
         (revappend (make-character-list x)
                    (make-character-list y))))

(defthm
  first-n-ac-of-make-character-list
  (implies (and (<= i (len l)))
           (equal (first-n-ac i (make-character-list l)
                              (make-character-list ac))
                  (make-character-list (first-n-ac i l ac)))))

(defthm
  take-more
  (implies
   (and (true-listp l)
        (natp i)
        (>= i (len l)))
   (equal (binary-append (first-n-ac i l ac1) ac2)
          (revappend ac1
                     (binary-append l
                                    (make-list-ac (- i (len l)) nil ac2)))))
  :hints
  (("goal'" :induct (first-n-ac i l ac1))
   ("subgoal *1/6'''" :expand (make-list-ac i nil ac2))
   ("subgoal *1/1''" :use (:instance revappend-is-append-of-rev (x ac1)
                                     (y l)
                                     (z ac2)))))

(defthm
  take-of-take
  (implies (and (true-listp l)
                (natp m)
                (integerp n)
                (<= m n)
                (<= m (len l)))
           (equal (first-n-ac m (take n l) ac)
                  (first-n-ac m l ac)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable binary-append-take-nthcdr
                        first-n-ac-of-binary-append-1)
    :use ((:instance binary-append-take-nthcdr (ac nil)
                     (i n))
          (:instance first-n-ac-of-binary-append-1 (i m)
                     (x (first-n-ac n l nil))
                     (y (nthcdr n l)))))
   ("goal'4'" :in-theory (disable take-more)
    :use (:instance take-more (i n)
                    (ac1 nil)
                    (ac2 nil)))
   ("goal'6'"
    :in-theory (disable first-n-ac-of-binary-append-1)
    :use (:instance first-n-ac-of-binary-append-1 (i m)
                    (x l)
                    (y (make-list-ac (+ n (- (len l)))
                                     nil nil))))))

(defthm boolean-listp-of-revappend
  (implies (boolean-listp x)
           (equal (boolean-listp (revappend x y))
                  (boolean-listp y))))

(defthm boolean-listp-of-first-n-ac
  (implies (and (boolean-listp l)
                (boolean-listp ac))
           (boolean-listp (first-n-ac i l ac))))

(defthm consp-of-first-n-ac
  (iff (consp (first-n-ac i l ac))
       (or (consp ac) (not (zp i)))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nth.lisp, from where it was taken with thanks.
(defthm nth-of-make-list-ac
  (equal (nth n (make-list-ac m val acc))
         (if (< (nfix n) (nfix m))
             val
           (nth (- n (nfix m)) acc))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nth.lisp, from where it was taken with thanks.
(defthm nth-of-nthcdr
  (equal (nth n (nthcdr m x))
         (nth (+ (nfix n) (nfix m)) x)))

(defthmd intersect-with-subset
  (implies (and (subsetp-equal x y)
                (intersectp-equal x z))
           (intersectp-equal y z)))

(defthm update-nth-of-make-list
  (implies (and (integerp key) (>= key n) (natp n))
           (equal (update-nth key val (make-list-ac n l ac))
                  (make-list-ac n l (update-nth (- key n) val ac)))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/update-nth.lisp, from where it was taken with thanks.
(defthm nthcdr-of-update-nth
  (equal (nthcdr n1 (update-nth n2 val x))
         (if (< (nfix n2) (nfix n1))
             (nthcdr n1 x)
           (update-nth (- (nfix n2) (nfix n1)) val (nthcdr n1 x)))))

(defthmd car-of-assoc-equal
  (let ((sd (assoc-equal x alist)))
    (implies (consp sd) (equal (car sd) x))))

(defthm update-nth-of-update-nth
  (implies (not (equal (nfix key1) (nfix key2)))
           (equal (update-nth key1 val1 (update-nth key2 val2 l))
                  (update-nth key2 val2 (update-nth key1 val1 l)))))
